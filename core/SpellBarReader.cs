namespace EqSpells.Core
{
    using System;
    using System.Collections.Generic;
    using System.Drawing;
    using System.Drawing.Drawing2D;
    using System.Drawing.Imaging;
    using System.IO;

    using EqIcon;

    internal enum ReadOutcome
    {
        NotRunning,     // EverQuest is not running (or minimized)
        NoChange,       // every gem still shows the icon we already have
        Updated,        // at least one icon changed
        Unreadable,     // the bar could not be located with confidence
    }

    // Reads the nine spell gems straight from the EverQuest window, in-process.
    // Holds the icon library, the bar geometry and the current key images in memory,
    // so a polling cycle costs a window capture plus nine dot products.
    internal sealed class SpellBarReader
    {
        // EverQuest shows a variable number of spell gems: eight for most of a career,
        // then more as levels and AA unlock them, up to fourteen. Hosts expose all
        // fourteen keys and let the player assign whichever they use; slots the
        // character does not have read as empty.
        public const Int32 MaxGemCount = 14;
        // The bar is LOCATED on a fixed run of nine gems, and this is deliberately not
        // MaxGemCount. FindBar averages its score over the whole run, so counting cells
        // that fall below the bar on open world would sink the average under GridScore
        // and the bar would never be found at all. Nine is the run this recogniser was
        // tuned and proven on; anything past it is detected afterwards, per cell.
        private const Int32 LocateGems = 9;

        // A gem must still resemble its current icon by at least this much to be
        // considered unchanged. Below it, that gem is re-identified.
        private const Single WatchScore = 0.85f;
        // Confidence required to *replace* a displayed icon. A gem drawn with a recast
        // overlay matches random icons around 0.8, so this threshold keeps it stable.
        private const Single ChangeScore = 0.90f;
        // A challenger must beat the incumbent by this margin to take its place.
        private const Single Hysteresis = 0.05f;
        // Many EQ spells share art across ranks. If the best and second-best library
        // icons are this close, the match carries no real information: keep what we show
        // rather than pick confidently-wrong art.
        private const Single MinMargin = 0.02f;
        // Average score required to trust a grid.
        private const Single GridScore = 0.85f;
        // More mismatching gems than this means the geometry is probably wrong,
        // not the spells: re-locate the whole bar instead of re-identifying gems.
        private const Int32 MaxTargetedGems = 4;
        // Locating the bar from scratch sweeps the library over the window: expensive and
        // rare. Do not retry it more often than this after a failure.
        private const Int32 LocateRetrySeconds = 120;
        // Consecutive cycles where nothing could be identified before we suspect the
        // geometry rather than the game state. At 5 s a cycle this is ~2 minutes, which
        // a long fight can exceed but a moved window will too - and the Refresh key is
        // always the immediate way out.
        private const Int32 UnreadableStreakBeforeRelocate = 24;
        // Above this, the geometry is considered locked and no refinement is needed.
        private const Single GoodScore = 0.95f;
        // A spell icon is never this small on screen. Without an absolute floor the
        // pitch sweep can "find" an 11 px grid in background texture and lock onto it.
        private const Single MinIconPixels = 16f;
        private const Single MinStridePixels = 22f;
        // Cells that must individually clear ChangeScore for a located grid to be
        // believed. See IsPlausible for the full reasoning; 4 is low enough for a
        // character with a handful of memorised spells and a tail of empty sockets,
        // and still four independent 0.90 matches - which scenery does not produce.
        private const Int32 MinConfidentGems = 4;
        // Hard ceiling on a whole locate. Sweeping several bands x several pitch ranges,
        // each with its own climb, multiplies the cost: without this the search ran for
        // over ten minutes pegging a core instead of failing and backing off.
        private const Int32 LocateBudgetSeconds = 100;
        // The climb walks up one gem at a time and each step is a full sweep. Landing
        // more than a few gems below the top is already unlikely.
        private const Int32 MaxClimbSteps = 4;
        // Consecutive flat readings before declaring a gem slot empty. Deliberately
        // long: a cast flash or a recast overlay can wash a gem out for a moment, and
        // two cycles (ten seconds) was short enough that keys visibly blinked off and
        // back on during a fight. Un-memorising a spell is rare and never urgent, so
        // waiting a minute to be sure costs nothing.
        private const Int32 FlatStreakBeforeEmpty = 12;

        private sealed class Grid
        {
            public Single X, Y0, Size, Stride;
        }

        private sealed class GemState
        {
            public String Sheet;          // full path of the source sheet
            public Int32 Index = -1;
            public Single[] Norm24;       // descriptor of what is currently displayed
            public Byte[] Png;            // encoded key image
            public Single Score;
            public Boolean KnownEmpty;    // the slot holds no spell (distinct from "unknown")
            public Int32 FlatStreak;      // consecutive cycles reading as a flat patch
        }

        private readonly IPluginLog _log;
        private readonly Object _sync = new Object();
        private readonly Object _pngLock = new Object();   // guards GemState.Png only
        private readonly GemState[] _gems = new GemState[MaxGemCount];
        // How many gems this character actually shows. Established by the last full
        // locate and persisted, so a restart does not go back to assuming nine.
        private Int32 _gemCount = LocateGems;

        private List<LibIcon> _lib;
        private String _gameDir;
        private String _iconDir;
        private EqGame.UiSettings _ui;
        private Grid _grid;
        // Grid as established by the last full locate. RefineGrid hill-climbs towards the
        // icons currently displayed; if those were ever wrong it would optimise towards
        // the wrong thing, so the refinement is never allowed to wander far from here.
        private Grid _anchorGrid;
        private DateTime _lastLocateFailedUtc = DateTime.MinValue;
        // Anchor-shift confirmation across full reads: a narrow vote must repeat before
        // it may move the grid. See ClimbToTop.
        private Int32 _pendingShiftK;
        private Int32 _pendingShiftCount;
        private Int32 _unreadableStreak;

        public String DataDir { get; }
        public String IconsDir => Path.Combine(this.DataDir, "icons");
        public String LastStatus { get; private set; } = "never run";

        public event EventHandler IconsChanged;
        // Raised after every read so a key can show that the plugin is stuck.
        public event EventHandler<ReadOutcome> StatusChanged;

        private ReadOutcome Report(ReadOutcome outcome)
        {
            this.StatusChanged?.Invoke(this, outcome);
            return outcome;
        }

        public SpellBarReader(IPluginLog log, String dataDir)
        {
            this._log = log;
            this.DataDir = dataDir;
            for (var i = 0; i < MaxGemCount; i++)
            {
                this._gems[i] = new GemState();
            }
            this.LoadState();
        }

        // Returns the PNG bytes, so each host can wrap them in whatever image type its
        // own SDK wants. Handing out a shared image object and disposing it on the next
        // update raced with the SDK drawing the key: the draw threw and Options+ showed
        // the action name instead of the icon. Bytes are immutable, so that cannot recur.
        //
        // Uses its own tiny lock, NOT _sync: Update() holds _sync for the whole read,
        // which can run a minute when the bar has to be located from scratch, and key
        // rendering must never queue behind that.
        public Byte[] GetIconPng(Int32 gem)
        {
            if (gem < 1 || gem > MaxGemCount) { return null; }
            lock (this._pngLock)
            {
                return this._gems[gem - 1].Png;
            }
        }

        // Drop the in-memory icon library (~17 MB). It is rebuilt on demand in ~130 ms.
        public void ReleaseLibrary()
        {
            lock (this._sync) { this._lib = null; }
        }

        // How many gems this character's bar actually has. Hosts expose all MaxGemCount
        // keys regardless - the player assigns whichever ones they use - but this says
        // which of them can ever show something.
        public Int32 GemCount => this._gemCount;

        public Boolean IsGemEmpty(Int32 gem)
        {
            if (gem < 1 || gem > MaxGemCount) { return false; }
            // Past the end of the bar there is nothing to read, which is a blank key for
            // the same reason an unmemorised slot is - not a gem we failed to identify.
            if (gem > this._gemCount) { return true; }
            return this._gems[gem - 1].KnownEmpty;
        }

        // --- Main entry point --------------------------------------------------

        public ReadOutcome Update(Boolean forceFull)
        {
            lock (this._sync)
            {
                var hwnd = EqGame.FindWindow();
                if (hwnd == IntPtr.Zero || EqGame.IsMinimized(hwnd))
                {
                    this.LastStatus = "EverQuest not running";
                    return this.Report(ReadOutcome.NotRunning);
                }

                using (var bmp = EqGame.Capture(hwnd))
                {
                    if (bmp == null)
                    {
                        this.LastStatus = "capture failed";
                        return this.Report(ReadOutcome.NotRunning);
                    }

                    if (!this.EnsureLibrary())
                    {
                        this.LastStatus = "icon pack not found";
                        return this.Report(ReadOutcome.Unreadable);
                    }

                    // Cheap path: does every gem still show what we already display?
                    // Only the spell bar is converted to floats here - a few thousand
                    // pixels instead of the window's several million.
                    if (!forceFull && this._grid != null)
                    {
                        var margin = 8;
                        var strip = FloatImg.FromBitmap(bmp,
                            (Int32)(this._grid.X - margin),
                            (Int32)(this._grid.Y0 - margin),
                            (Int32)(this._grid.Size + 2 * margin),
                            (Int32)((this._gemCount - 1) * this._grid.Stride + this._grid.Size + 2 * margin));

                        // The stored grid is only as precise as the last full locate, and
                        // sub-pixel drift alone drops every score enough to look like a
                        // change. Re-lock it on the icons we already know before judging.
                        var scores = this.GemScores(strip, this._grid);
                        if (WorstScore(scores) < GoodScore)
                        {
                            this.RefineGrid(strip);
                            scores = this.GemScores(strip, this._grid);
                        }

                        // Every gem unreadable while we do know what they should look like
                        // means the capture itself is blank, not that the spells changed.
                        // Treating that as "unchanged" would freeze stale icons forever.
                        var readable = 0;
                        var known = 0;
                        for (var i = 0; i < this._gemCount; i++)
                        {
                            if (!Single.IsNaN(scores[i])) { readable++; }
                            if (this._gems[i].Norm24 != null) { known++; }
                        }
                        if (readable == 0 && known > 0)
                        {
                            this.LastStatus = "capture unreadable";
                            return this.Report(ReadOutcome.Unreadable);
                        }

                        // A gem reading flat while others read fine is an empty slot, not
                        // a broken capture: clear its key instead of leaving a stale spell.
                        var emptied = 0;
                        for (var i = 0; i < this._gemCount; i++)
                        {
                            var st = this._gems[i];
                            var flat = Single.IsNaN(scores[i]) && st.Norm24 != null;
                            if (flat)
                            {
                                st.FlatStreak++;
                                // Milestones only: this branch runs every cycle for a
                                // minute before anything visible happens, and that
                                // silence once cost an evening of blind guessing.
                                if (st.FlatStreak == 1 || st.FlatStreak == FlatStreakBeforeEmpty / 2)
                                {
                                    this._log?.Info($"Gem {i + 1} reads flat (streak {st.FlatStreak}/{FlatStreakBeforeEmpty})");
                                }
                                if (st.FlatStreak >= FlatStreakBeforeEmpty && !st.KnownEmpty)
                                {
                                    this.ClearGem(i);
                                    emptied++;
                                }
                            }
                            else if (!Single.IsNaN(scores[i]) && scores[i] >= WatchScore)
                            {
                                // Only an actual re-match of the displayed icon resets the
                                // countdown. Resetting on any readable patch let an empty
                                // socket stall the clear for half an hour: at a sliver of
                                // grid drift the socket sometimes normalises as noise,
                                // scores ~0.3, and that noise kept being taken as "the
                                // spell is back". Instrumentation caught it as a streak
                                // restarting from 1 every few minutes. A genuinely busy
                                // gem (cast flash, cooldown tint) is structured, not flat,
                                // so the streak does not grow through a fight either way.
                                if (st.FlatStreak >= 3)
                                {
                                    this._log?.Info($"Gem {i + 1} flat streak reset at {st.FlatStreak} (score {scores[i]:F2})");
                                }
                                st.FlatStreak = 0;
                            }
                        }

                        var suspicious = new List<Int32>();
                        var knownSuspicion = false;
                        for (var i = 0; i < this._gemCount; i++)
                        {
                            var st = this._gems[i];
                            if (st.Norm24 != null)
                            {
                                if (!Single.IsNaN(scores[i]) && scores[i] < WatchScore)
                                {
                                    suspicious.Add(i);
                                    knownSuspicion = true;
                                }
                                continue;
                            }
                            // No descriptor: either never identified, or a slot we blanked.
                            // Either way the only question is whether something is there
                            // now. Skipping blanked gems here made "empty" a one-way trip -
                            // re-memorising a spell could never light the key again.
                            var probe = strip.Patch(this._grid.X, this._grid.Y0 + i * this._grid.Stride,
                                this._grid.Size, this._grid.Size, 24);
                            if (Matcher.Normalize(probe)) { suspicious.Add(i); }
                        }
                        if (suspicious.Count == 0 && emptied > 0)
                        {
                            this._unreadableStreak = 0;
                            this.SaveState();
                            this.IconsChanged?.Invoke(this, EventArgs.Empty);
                            this.LastStatus = $"{emptied} slot(s) now empty";
                            return this.Report(ReadOutcome.Updated);
                        }
                        if (suspicious.Count == 0)
                        {
                            this._unreadableStreak = 0;
                            this.LastStatus = "unchanged";
                            return this.Report(ReadOutcome.NoChange);
                        }
                        // Re-identify whatever no longer matches, however many. Assuming
                        // "more than N gems differ, so the geometry must be wrong" was a
                        // mistake: swapping a whole spell set is routine, and it sent the
                        // plugin into a minute-long relocate that produced no icons at all.
                        // Only fall through to relocating when the gems cannot be
                        // identified at all, which is what a bad grid actually looks like.
                        var n = this.ReidentifyGems(strip, suspicious);
                        if (n > 0)
                        {
                            this._unreadableStreak = 0;
                            this.LastStatus = $"{n} icon(s) updated";
                            this.SaveState();
                            this.IconsChanged?.Invoke(this, EventArgs.Empty);
                            return this.Report(ReadOutcome.Updated);
                        }
                        // Nothing could be identified. In combat EverQuest tints and
                        // darkens the gems for minutes on end, so this is the normal
                        // state of a busy fight - not a sign the geometry moved. Keep
                        // showing what we have and only consider relocating after a long
                        // sustained streak; the Refresh key forces it at any time.
                        // Blind probes of unknown slots failing to identify is the NORMAL
                        // state of an empty-but-textured cell (a phantom slot kept by the
                        // sticky count, scenery under a short bar). Only a KNOWN gem that
                        // stopped matching is evidence the geometry may be wrong; without
                        // one, this cycle must not wind the relocate counter.
                        if (!knownSuspicion)
                        {
                            this.LastStatus = "unchanged";
                            return this.Report(ReadOutcome.NoChange);
                        }
                        this._unreadableStreak++;
                        if (this._unreadableStreak == 1 || this._unreadableStreak == UnreadableStreakBeforeRelocate / 2)
                        {
                            var which = String.Join(",", suspicious.ConvertAll(x => (x + 1).ToString(System.Globalization.CultureInfo.InvariantCulture)));
                            this._log?.Info($"Gem(s) {which} unidentifiable (streak {this._unreadableStreak}/{UnreadableStreakBeforeRelocate})");
                        }
                        if (this._unreadableStreak < UnreadableStreakBeforeRelocate)
                        {
                            this.LastStatus = $"gem(s) in transition ({this._unreadableStreak})";
                            return this.Report(ReadOutcome.NoChange);
                        }
                    }

                    // Expensive path: (re)locate the bar over the whole window, then
                    // identify all nine gems. Sweeping the library over the window takes
                    // tens of seconds, so after a failure (bar hidden, character select,
                    // login screen) back off instead of burning a core every cycle.
                    if (!forceFull && this._lastLocateFailedUtc != DateTime.MinValue &&
                        (DateTime.UtcNow - this._lastLocateFailedUtc).TotalSeconds < LocateRetrySeconds)
                    {
                        this.LastStatus = "spell bar not found (retry deferred)";
                        return this.Report(ReadOutcome.Unreadable);
                    }

                    var screen = FloatImg.FromBitmap(bmp);
                    var grid = this.LocateBar(screen);
                    if (grid == null)
                    {
                        this._lastLocateFailedUtc = DateTime.UtcNow;
                        this.LastStatus = "spell bar not found";
                        return this.Report(ReadOutcome.Unreadable);
                    }
                    this._lastLocateFailedUtc = DateTime.MinValue;
                    this._grid = grid;
                    this._anchorGrid = new Grid { X = grid.X, Y0 = grid.Y0, Size = grid.Size, Stride = grid.Stride };

                    // The bar may have got shorter since the last locate - a different
                    // character on the same account, or a UI layout change. Slots that no
                    // longer exist must go blank rather than keep the previous character's
                    // art on a key that now casts nothing.
                    for (var i = this._gemCount; i < MaxGemCount; i++)
                    {
                        if (this._gems[i].Sheet != null) { this.ClearGem(i); }
                    }

                    var all = new List<Int32>();
                    for (var i = 0; i < this._gemCount; i++) { all.Add(i); }
                    var changed = this.ReidentifyGems(screen, all);
                    this.SaveState();
                    this.LastStatus = changed > 0 ? $"{changed} icon(s) updated" : "unchanged";
                    if (changed > 0)
                    {
                        this.IconsChanged?.Invoke(this, EventArgs.Empty);
                        return this.Report(ReadOutcome.Updated);
                    }
                    return this.Report(ReadOutcome.NoChange);
                }
            }
        }

        // --- Watch pass --------------------------------------------------------

        // How well each gem still matches the icon it currently displays.
        // NaN means "no information": a flat patch (empty slot, spell being scribed) or
        // a gem we have never identified. It must not be read as "this gem changed".
        private Single[] GemScores(FloatImg img, Grid g)
        {
            var outp = new Single[this._gemCount];
            for (var i = 0; i < this._gemCount; i++)
            {
                var st = this._gems[i];
                if (st.Norm24 == null) { outp[i] = Single.NaN; continue; }
                var p = img.Patch(g.X, g.Y0 + i * g.Stride, g.Size, g.Size, 24);
                outp[i] = Matcher.Normalize(p) ? Matcher.Dot(p, st.Norm24) : Single.NaN;
            }
            return outp;
        }

        private static Single WorstScore(Single[] scores)
        {
            var worst = Single.MaxValue;
            var any = false;
            foreach (var s in scores)
            {
                if (Single.IsNaN(s)) { continue; }
                any = true;
                if (s < worst) { worst = s; }
            }
            return any ? worst : Single.NaN;
        }

        private static Single MeanScore(Single[] scores)
        {
            Single sum = 0;
            var n = 0;
            foreach (var s in scores)
            {
                if (Single.IsNaN(s)) { continue; }
                sum += s;
                n++;
            }
            return n == 0 ? Single.NaN : sum / n;
        }

        // Refinement may only nudge the geometry, never walk it to another bar.
        private Boolean WithinAnchor(Grid g)
        {
            var a = this._anchorGrid;
            if (a == null) { return true; }
            const Single maxDrift = 3f;
            return Math.Abs(g.X - a.X) <= maxDrift
                && Math.Abs(g.Y0 - a.Y0) <= maxDrift
                && Math.Abs(g.Size - a.Size) <= maxDrift
                && Math.Abs(g.Stride - a.Stride) <= 1f;
        }

        // Nudge the grid so it best explains the icons we already display. Nine known
        // templates instead of the whole library makes this a few milliseconds, and it
        // keeps the geometry locked sub-pixel between full locates.
        private void RefineGrid(FloatImg strip)
        {
            var g = this._grid;
            var bestScore = MeanScore(this.GemScores(strip, g));
            if (Single.IsNaN(bestScore)) { return; }
            var best = g;

            foreach (var dx in new[] { -0.5f, -0.25f, 0f, 0.25f, 0.5f })
            {
                foreach (var dy in new[] { -0.5f, -0.25f, 0f, 0.25f, 0.5f })
                {
                    foreach (var dsz in new[] { -0.5f, 0f, 0.5f })
                    {
                        foreach (var dst in new[] { -0.125f, 0f, 0.125f })
                        {
                            var cand = new Grid
                            {
                                X = g.X + dx,
                                Y0 = g.Y0 + dy,
                                Size = g.Size + dsz,
                                Stride = g.Stride + dst,
                            };
                            if (!this.WithinAnchor(cand)) { continue; }
                            var s = MeanScore(this.GemScores(strip, cand));
                            if (!Single.IsNaN(s) && s > bestScore) { bestScore = s; best = cand; }
                        }
                    }
                }
            }
            this._grid = best;
        }

        // --- Identification ----------------------------------------------------

        // Re-identify the given gems against the library. Returns how many icons changed.
        private Int32 ReidentifyGems(FloatImg screen, List<Int32> gems)
        {
            var changed = 0;
            foreach (var i in gems)
            {
                var st = this._gems[i];
                var p = screen.Patch(this._grid.X, this._grid.Y0 + i * this._grid.Stride, this._grid.Size, this._grid.Size, 24);
                if (!Matcher.Normalize(p))
                {
                    // Flat: an empty socket. Clear the key rather than keep a stale spell.
                    if (!this._gems[i].KnownEmpty) { this.ClearGem(i); changed++; }
                    continue;
                }

                LibIcon best = null, second = null;
                Single bestScore = -1, secondScore = -1;
                foreach (var li in this._lib)
                {
                    var s = Matcher.Dot(p, li.Norm24);
                    if (s > bestScore) { secondScore = bestScore; second = best; bestScore = s; best = li; }
                    else if (s > secondScore) { secondScore = s; second = li; }
                }
                if (best == null) { continue; }

                // Stickiness: how well does what we already show explain this capture?
                var incumbent = st.Norm24 != null ? Matcher.Dot(p, st.Norm24) : -1f;

                var sameAsBefore = st.Sheet != null && st.Sheet == best.Sheet && st.Index == best.Index;
                if (sameAsBefore)
                {
                    st.Score = bestScore;
                    // The descriptor and the image are what the cheap path relies on. A
                    // state restored from disk has neither, and forgetting to fill them
                    // here makes every gem look suspicious forever, which sends every
                    // cycle down the expensive path.
                    st.Norm24 = best.Norm24;
                    if (st.Png == null) { this.ApplyIcon(i, best, bestScore); }
                    continue;
                }
                // Only swap on a confident, clearly better match. A gem mid-recast never
                // reaches this bar, so its icon stays put.
                if (bestScore < ChangeScore || bestScore < incumbent + Hysteresis) { continue; }
                // A thin margin only means ambiguity when the two candidates are
                // different pictures. EverQuest ships near-identical art for several
                // spells (all the healing hearts, for instance), so demanding a margin
                // there rejected a perfectly good match forever - the key stayed blank.
                if (bestScore - secondScore < MinMargin && second != null &&
                    Matcher.Dot(best.Norm24, second.Norm24) < 0.99f)
                {
                    continue;
                }

                if (this.ApplyIcon(i, best, bestScore)) { changed++; }
            }
            return changed;
        }

        // Blank a key: the slot holds no spell.
        private void ClearGem(Int32 gemIndex)
        {
            var st = this._gems[gemIndex];
            lock (this._pngLock) { st.Png = null; }
            st.Sheet = null;
            st.Index = -1;
            st.Norm24 = null;
            st.Score = 0;
            st.KnownEmpty = true;
            st.FlatStreak = 0;
            try
            {
                var f = Path.Combine(this.IconsDir, $"spell_{gemIndex + 1}.png");
                if (File.Exists(f)) { File.Delete(f); }
            }
            catch (Exception) { }
        }

        private Boolean ApplyIcon(Int32 gemIndex, LibIcon icon, Single score)
        {
            try
            {
                using (var bmp40 = CropSheet(icon))
                {
                    if (bmp40 == null) { return false; }
                    var png = EncodeScaledPng(bmp40, 128);
                    var st = this._gems[gemIndex];
                    lock (this._pngLock) { st.Png = png; }
                    st.Sheet = icon.Sheet;
                    st.KnownEmpty = false;
                    st.FlatStreak = 0;
                    st.Index = icon.Index;
                    st.Norm24 = icon.Norm24;
                    st.Score = score;
                    this.WriteDebugPng(gemIndex + 1, png);
                }
                return true;
            }
            catch (Exception ex)
            {
                this._log?.Warning($"Cannot build icon for gem {gemIndex + 1}: {ex.Message}");
                return false;
            }
        }

        private static Bitmap CropSheet(LibIcon icon)
        {
            using (var full = Tga.Load(icon.Sheet))
            {
                if (full == null) { return null; }
                var cell = icon.CellSize;
                var cols = full.Width / cell;
                var sx = (icon.Index % cols) * cell;
                var sy = (icon.Index / cols) * cell;
                var outp = new Bitmap(cell, cell, PixelFormat.Format32bppArgb);
                using (var g = Graphics.FromImage(outp))
                {
                    g.DrawImage(full, new Rectangle(0, 0, cell, cell), sx, sy, cell, cell, GraphicsUnit.Pixel);
                }
                return outp;
            }
        }

        // Nearest-neighbour upscale keeps the pixel-art crisp on the key display.
        private static Byte[] EncodeScaledPng(Bitmap src, Int32 size)
        {
            using (var big = new Bitmap(size, size, PixelFormat.Format32bppArgb))
            {
                using (var g = Graphics.FromImage(big))
                {
                    g.InterpolationMode = InterpolationMode.NearestNeighbor;
                    g.PixelOffsetMode = PixelOffsetMode.Half;
                    g.DrawImage(src, 0, 0, size, size);
                }
                using (var ms = new MemoryStream())
                {
                    big.Save(ms, ImageFormat.Png);
                    return ms.ToArray();
                }
            }
        }

        private void WriteDebugPng(Int32 gemNumber, Byte[] png)
        {
            try
            {
                Directory.CreateDirectory(this.IconsDir);
                File.WriteAllBytes(Path.Combine(this.IconsDir, $"spell_{gemNumber}.png"), png);
            }
            catch (Exception)
            {
                // Debug output only; never fail the update because of it.
            }
        }

        // --- Locating the bar --------------------------------------------------

        private Grid LocateBar(FloatImg screen)
        {
            // 1. Revalidate the grid we already know, on the run length we last agreed on.
            // The window is +/-4 px: the bar drifts a few pixels over days of play, and
            // falling through to the band sweep is exactly what a full bar cannot afford
            // (see ClimbToTop for why).
            if (this._grid != null)
            {
                var run = Math.Min(this._gemCount, LocateGems);
                var fit = Matcher.FindBar(screen, this._lib,
                    this._grid.X - 4, this._grid.X + 4, this._grid.Y0 - 4, this._grid.Y0 + 4,
                    this._grid.Size - 1, this._grid.Size + 1, this._grid.Stride - 0.25f, this._grid.Stride + 0.25f, run);
                if (IsPlausible(fit))
                {
                    // Recount here too. Every full read takes this fast path while the
                    // bar has not moved, so counting only on the band sweep left the
                    // Refresh key unable to pick up slots a stale save undercounted -
                    // the one job it was added for.
                    var g = this.ClimbToTop(screen, ToGrid(fit));
                    this._gemCount = this.CountGems(screen, g, fit);
                    return g;
                }
            }

            // 2. Locate by structure: the gems repeat at a fixed vertical stride, which
            //    is found over the full window height in milliseconds.
            // Candidate horizontal bands to sweep, most likely first. The spell window
            // can be docked against either edge: XRef says which edge XPos is measured
            // from, and reading XPos while ignoring XRef would send the search to the
            // wrong side of the screen for a right-docked bar.
            var bands = new List<Int32[]>();
            if (this._ui?.BarXPercent != null)
            {
                var pct = this._ui.BarXPercent.Value;
                var anchoredRight = this._ui.BarXRef != null && this._ui.BarXRef.StartsWith("right", StringComparison.Ordinal);
                var seed = anchoredRight
                    ? (Int32)(screen.W + screen.W * pct / 100.0)
                    : (Int32)(screen.W * pct / 100.0);
                bands.Add(new[] { Math.Max(0, seed - 25), Math.Min(screen.W - 1, seed + 35) });
            }
            // Fallbacks, in case the UI file is missing or says something unexpected.
            bands.Add(new[] { 0, 100 });
            bands.Add(new[] { Math.Max(0, screen.W - 130), screen.W - 1 });

            var xLo = bands[0][0];
            var xHi = bands[0][1];

            // Proven range, deliberately narrow. Widening it let the periodicity lock
            // onto a harmonic and the bar was read four gems too low; and picking the
            // "topmost alignment that still scores" read it four gems too high, because
            // best-match-over-2262-icons stays high on plain background - it says which
            // icon is closest, never whether an icon is there at all.
            // EverQuest offers several spell-bar layouts (normal gems, small gems, small
            // with text, small with text and numbers). They all stack square icons at a
            // fixed vertical pitch, but the pitch differs a lot between them, and so does
            // the Windows/UI scaling on top.
            //
            // Each range is swept SEPARATELY and kept narrow on purpose. One wide range
            // lets the periodicity lock onto a harmonic of the true pitch - that is how
            // the bar once got read four gems too low, shifting every icon silently.
            BarFit best = null;
            var deadline = DateTime.UtcNow.AddSeconds(LocateBudgetSeconds);
            foreach (var band in bands)
            {
                foreach (var pitch in PitchRanges)
                {
                    if (DateTime.UtcNow > deadline)
                    {
                        this._log?.Info("Locate budget exhausted; giving up for now");
                        break;
                    }
                    var cand = this.LocateInBand(screen, band[0], band[1], pitch[0], pitch[1], LocateGems);
                    if (IsPlausible(cand) && (best == null || Average(cand) > Average(best))) { best = cand; }
                    if (IsPlausible(best)) { break; }
                }
                if (IsPlausible(best) || DateTime.UtcNow > deadline) { break; }
            }
            var found = best;
            // Nothing plausible in any band: fail cleanly. Falling through with null took
            // ChooseBestPack down with a NullReferenceException, and an exception here
            // skips the caller's back-off - so a hidden bar re-ran a full-budget locate
            // every cycle instead of retrying in 2 minutes.
            if (found == null) { return null; }

            // 4. Now that the gems are located, check we are reading the icon pack the
            //    game actually draws; if not, switch and re-match against the winner.
            if (this.ChooseBestPack(screen, found))
            {
                found = Matcher.FindBar(screen, this._lib,
                    found.X - 0.5f, found.X + 0.5f, found.Y0 - 0.5f, found.Y0 + 0.5f,
                    found.Scale - 0.5f, found.Scale + 0.5f, found.Stride - 0.25f, found.Stride + 0.25f, LocateGems);
            }

            if (!IsPlausible(found)) { return null; }
            var grid = this.ClimbToTop(screen, ToGrid(found));
            this._gemCount = this.CountGems(screen, grid, found);
            return grid;
        }

        // A fully-memorised bar is translation-degenerate: a nine-cell fit is equally
        // perfect starting at slot 1 or slot 5 - fourteen icons offer six flawless
        // alignments - and the sweep once locked four gems low, then REVALIDATED its own
        // mistake every cycle, since nine cells from slot 5 are also all icons.
        //
        // Anchoring by stepping toward "no icon above" was tried and failed both ways in
        // one afternoon: a slot mid-pulse under Symphonic Aura reads as non-icon and
        // stops the climb short, and whatever sits above the bar can read AS an icon and
        // walks it past the top - the exact failure the original sweep comments warned
        // about. Single-cell boundary tests lose to single-frame noise, full stop.
        //
        // So the anchor is a vote instead. Every vertical alignment within a slot's
        // reach scores one point per cell that reads as bar material (an icon at
        // WatchScore, or flat like an empty socket) across the WHOLE bar length. Only
        // the true alignment keeps all its cells inside the bar; every shifted one
        // pays for each cell hanging over the spellbook button, scenery, or the buff
        // stack above - and a couple of pulse-washed cells cost every alignment about
        // equally. Ties break toward the weakest icon-evidence above the top, which is
        // what "this is really the first slot" looks like.
        private Grid ClimbToTop(FloatImg screen, Grid g)
        {
            var reach = MaxGemCount - LocateGems + 1;
            var bestK = 0;
            var bestScore = -1;
            var currentScore = 0;
            var bestAbove = Single.MaxValue;
            for (var k = -reach; k <= reach; k++)
            {
                var top = g.Y0 + k * g.Stride;
                if (top < 0 || top + (this._gemCount - 1) * g.Stride + g.Size > screen.H) { continue; }
                var score = 0;
                for (var i = 0; i < this._gemCount; i++)
                {
                    var y = top + i * g.Stride;
                    var p = screen.Patch(g.X, y, g.Size, g.Size, 24);
                    if (!Matcher.Normalize(p)) { score++; continue; }
                    if (Matcher.ScoreCell(screen, this._lib, g.X, y, g.Size) >= WatchScore) { score++; }
                }
                var yAbove = top - g.Stride;
                var above = yAbove >= 0 ? Matcher.ScoreCell(screen, this._lib, g.X, yAbove, g.Size) : 0f;
                if (k == 0) { currentScore = score; }
                if (score > bestScore || (score == bestScore && above < bestAbove))
                {
                    bestScore = score;
                    bestAbove = above;
                    bestK = k;
                }
            }
            if (bestK == 0)
            {
                this._pendingShiftK = 0;
                return g;
            }

            // A narrow vote must not move the grid on one frame. Something above the bar
            // reads icon-like, so whenever a cast washes a bottom slot the one-up
            // alignment edges out the truth by a single point - and the anchor was seen
            // ping-ponging -1/+1 four times in a minute of active play. Washes move to a
            // different cell every frame, so a spurious winner cannot repeat, while a
            // genuinely shifted grid proposes the same correction on every read. Hence:
            // a landslide (the 13:07 four-slot lock won by a margin of 3+) applies
            // immediately, a narrow winner must propose the SAME shift on two
            // consecutive full reads.
            var margin = bestScore - currentScore;
            if (margin < 3)
            {
                if (this._pendingShiftK == bestK && this._pendingShiftCount >= 1)
                {
                    // Confirmed on a second independent frame; fall through and apply.
                }
                else
                {
                    this._pendingShiftK = bestK;
                    this._pendingShiftCount = 1;
                    this._log?.Info($"Bar anchor shift of {bestK} proposed ({bestScore} vs {currentScore} cells); awaiting confirmation");
                    return g;
                }
            }
            this._pendingShiftK = 0;
            this._pendingShiftCount = 0;

            var fit = Matcher.FindBar(screen, this._lib,
                g.X - 1, g.X + 1, g.Y0 + bestK * g.Stride - 1, g.Y0 + bestK * g.Stride + 1,
                g.Size - 1, g.Size + 1, g.Stride - 0.25f, g.Stride + 0.25f, LocateGems);
            if (!IsPlausible(fit)) { return g; }
            this._log?.Info($"Bar anchor corrected by {bestK} slot(s) ({bestScore}/{this._gemCount} cells agree)");
            return ToGrid(fit);
        }

        // How many slots this bar actually has. The fit only proves the first LocateGems
        // cells; walk down from there and keep every cell that reads as part of the bar.
        //
        // A cell belongs to the bar if it holds an icon or an empty socket. Measured on
        // real frames: a socket is simply FLAT at 24 px (the watch pass's own signature
        // for an emptied slot), an icon matches the library, and whatever sits below the
        // bar is textured without matching - the spellbook button scores ~0.6, scenery
        // likewise - so "structured but not an icon" is where the bar ends.
        //
        // Two hard-won rules make the walk robust:
        //
        //  - The icon test uses WatchScore, not ChangeScore. This is a boundary check,
        //    not an art change: a cell at 0.86 is overwhelmingly an icon (open world
        //    peaks near 0.8), and demanding 0.90 made the count a coin-toss on a cell
        //    that measured 0.900 exactly on a clean frame.
        //
        //  - The count is STICKY: one ambiguous frame can extend the bar but never
        //    shorten it. Symphonic Aura pulses the bottom slots forever, and a cell
        //    caught mid-cast is structured-but-matching-nothing - one such frame used
        //    to amputate the bar to nine, persist it, and kill keys 10-14 until the
        //    next lucky recount. The cost: a genuinely shorter bar (another character)
        //    keeps a few phantom slots whose keys simply stay blank, until a state
        //    reset re-counts from scratch.
        private Int32 CountGems(FloatImg screen, Grid g, BarFit fit)
        {
            var n = LocateGems;
            for (var i = LocateGems; i < MaxGemCount; i++)
            {
                var y = g.Y0 + i * g.Stride;
                if (y + g.Size > screen.H) { break; }
                var p = screen.Patch(g.X, y, g.Size, g.Size, 24);
                var isFlatSocket = !Matcher.Normalize(p);
                var isIcon = !isFlatSocket &&
                    Matcher.ScoreCell(screen, this._lib, g.X, y, g.Size) >= WatchScore;
                var wasBar = i < this._gemCount;
                if (!isIcon && !isFlatSocket && !wasBar) { break; }
                n = i + 1;
            }
            if (n < this._gemCount) { n = this._gemCount; }
            if (n != this._gemCount) { this._log?.Info($"Spell bar has {n} slot(s)"); }
            return n;
        }


        // Sweep one horizontal band: find the vertical pitch, lock the grid on it, then
        // climb to the topmost gem.
        // Plausible vertical pitches, most common first. Narrow on purpose - see the
        // comment at the call site about harmonics.
        private static readonly Single[][] PitchRanges =
        {
            new[] { 38f, 47f },   // normal gems at 100% scaling (the common case)
            new[] { 28f, 38f },   // the "small gems" layouts
            new[] { 47f, 60f },   // normal gems on a scaled-up display
            new[] { 20f, 28f },   // small gems on a scaled-down display
            new[] { 60f, 85f },   // heavily scaled up
        };

        private BarFit LocateInBand(FloatImg screen, Int32 xLo, Int32 xHi, Single pitchLo, Single pitchHi, Int32 run)
        {
            var per = Matcher.FindGridPeriodic(screen, xLo, xHi + 45, pitchLo, pitchHi, 0.5f, run);
            var py = per[0];
            var ps = per[1];
            // The icon does not fill its cell the same way in every skin: the classic
            // skins draw 24 px inside a 40 px cell (0.60) while default_modern draws
            // 36 px (0.90). A 0.72 floor silently excluded the classic skins entirely.
            var szLo = (Int32)Math.Max(14, ps * 0.50f);
            var szHi = (Int32)(ps * 0.98f);

            // The y window reaches TWO extra strides below the periodic phase. The phase
            // marks where stride-periodic structure STARTS, and on self-similar ground
            // (a grass field correlates with itself at any stride) that start can be a
            // stride or two ABOVE the bar's first gem. The climb below only ever walks
            // up, so a phase above the bar used to put the true y0 outside the search
            // entirely - the bar was pixel-perfect on screen and never found. With the
            // window covering both cases, the nine-cell optimiser decides: nine real
            // icons always outscore a shifted run that swaps gems for ground.
            var found = Matcher.FindBar(screen, this._lib,
                xLo, xHi + 20, py - ps / 2 - 4, py + 2 * ps + ps / 2 + 4, szLo, szHi, ps - 1, ps + 1, run);

            // 3. Climb one gem at a time while the cell above still reads as an icon.
            for (var up = 0; up < MaxClimbSteps; up++)
            {
                var yAbove = found.Y0 - found.Stride;
                if (yAbove < 0) { break; }
                if (Matcher.ScoreCell(screen, this._lib, found.X, yAbove, found.Scale) < 0.80f) { break; }
                found = Matcher.FindBar(screen, this._lib,
                    found.X - 1, found.X + 1, yAbove - 1, yAbove + 1,
                    found.Scale - 1, found.Scale + 1, found.Stride - 0.5f, found.Stride + 0.5f, run);
            }
            return found;
        }

        private static Grid ToGrid(BarFit f) => new Grid { X = f.X, Y0 = f.Y0, Size = f.Scale, Stride = f.Stride };

        // Is this a believable spell bar, or scenery that happens to repeat?
        //
        // Judged on the BEST cells, not on all of them, because empty slots are part of
        // any normal bar and score near zero against a library of spell icons. Averaging
        // over the whole run meant a cold locate could only ever succeed on a bar that
        // was mostly full - which is exactly how the first cold start with six memorised
        // spells and a tail of empty sockets failed to find a perfectly visible bar.
        //
        // What still keeps scenery out:
        //  - MinConfidentGems cells must each clear ChangeScore (0.90) individually.
        //    That per-cell bar is the strong gate: open world peaks near 0.8, and the
        //    one false grid ever observed averaged well while no single cell convinced.
        //  - The best cells must also average GridScore, so the confident quota cannot
        //    be carried by four lucky cells amid garbage.
        //  - The absolute size floors, which killed the 11 px grid found in a texture.
        // The price: a character with fewer than four identifiable spells memorised
        // cannot be calibrated from scratch. Memorise four, calibrate once, and the
        // watch pass tracks any number from then on.
        private static Boolean IsPlausible(BarFit f)
        {
            if (f == null || f.Gems == null || f.Gems.Count == 0) { return false; }
            if (f.Scale < MinIconPixels || f.Stride < MinStridePixels) { return false; }
            var scores = new List<Single>();
            var confident = 0;
            foreach (var g in f.Gems)
            {
                scores.Add(g.Score);
                if (g.Score >= ChangeScore) { confident++; }
            }
            if (confident < MinConfidentGems) { return false; }
            scores.Sort();
            scores.Reverse();
            Single sum = 0;
            var k = Math.Min(6, scores.Count);
            for (var i = 0; i < k; i++) { sum += scores[i]; }
            return sum / k >= GridScore;
        }

        private static Single Average(BarFit f)
        {
            if (f?.Gems == null || f.Gems.Count == 0) { return 0; }
            Single sum = 0;
            foreach (var g in f.Gems) { sum += g.Score; }
            return sum / f.Gems.Count;
        }

        // --- Library -----------------------------------------------------------

        private Boolean EnsureLibrary()
        {
            if (this._lib != null && this._lib.Count > 0) { return true; }

            this._gameDir = this._gameDir ?? EqGame.FindGameDir();
            if (this._gameDir == null) { return false; }
            this._ui = this._ui ?? EqGame.ReadUiSettings(this._gameDir);

            var packs = EqGame.FindIconPacks(this._gameDir, this._ui.Skin);
            if (packs.Count == 0)
            {
                // The remembered folder no longer holds icons (game moved or reinstalled).
                // Forget it so the next cycle rediscovers instead of failing forever.
                this._log?.Warning($"No icon pack under '{this._gameDir}' - forgetting it");
                this._gameDir = null;
                this._iconDir = null;
                this._ui = null;
                return false;
            }

            // Reuse the pack chosen previously; otherwise start with the first and let
            // ChooseBestPack correct it once the bar is located.
            var dir = (this._iconDir != null && Directory.Exists(this._iconDir)) ? this._iconDir : packs[0];
            this._lib = Matcher.LoadLibrary(dir, "Spells*.tga", 40, 107, 107, 107);
            this._iconDir = dir;
            this._log?.Info($"Icon pack '{Path.GetFileName(dir)}' loaded ({this._lib.Count} icons, {packs.Count} distinct pack(s))");
            return this._lib.Count > 0;
        }

        // Score every distinct pack against the located gems and keep the best.
        // Returns true when the active pack changed.
        private Boolean ChooseBestPack(FloatImg screen, BarFit fit)
        {
            var packs = EqGame.FindIconPacks(this._gameDir, this._ui.Skin);
            if (packs.Count < 2) { return false; }
            var bestDir = this._iconDir;
            var bestScore = Matcher.ScorePack(screen, this._lib, fit);
            List<LibIcon> bestLib = null;
            foreach (var dir in packs)
            {
                if (dir == this._iconDir) { continue; }
                var trial = Matcher.LoadLibrary(dir, "Spells*.tga", 40, 107, 107, 107);
                var s = Matcher.ScorePack(screen, trial, fit);
                if (s > bestScore + 0.01f) { bestScore = s; bestDir = dir; bestLib = trial; }
            }
            if (bestLib == null) { return false; }

            this._log?.Info($"Switching icon pack to '{Path.GetFileName(bestDir)}' (score {bestScore:F3})");
            this._iconDir = bestDir;
            this._lib = bestLib;
            // Descriptors from the old pack are meaningless now.
            foreach (var st in this._gems) { st.Norm24 = null; st.Sheet = null; st.Index = -1; }
            return true;
        }

        // --- Persistence -------------------------------------------------------

        private String StatePath => Path.Combine(this.DataDir, "barstate.txt");

        private void SaveState()
        {
            try
            {
                Directory.CreateDirectory(this.DataDir);
                var lines = new List<String>();
                if (this._grid != null)
                {
                    // Invariant culture on purpose: interpolation would use the machine's
                    // locale and write "22,25", which the invariant parser then rejects -
                    // silently losing the calibration on every restart.
                    var inv = System.Globalization.CultureInfo.InvariantCulture;
                    lines.Add("grid=" + String.Join("|", new[]
                    {
                        this._grid.X.ToString("R", inv),
                        this._grid.Y0.ToString("R", inv),
                        this._grid.Size.ToString("R", inv),
                        this._grid.Stride.ToString("R", inv),
                    }));
                }
                lines.Add("gems=" + this._gemCount.ToString(System.Globalization.CultureInfo.InvariantCulture));
                if (this._iconDir != null) { lines.Add("iconDir=" + this._iconDir); }
                if (this._gameDir != null) { lines.Add("gameDir=" + this._gameDir); }
                for (var i = 0; i < MaxGemCount; i++)
                {
                    var st = this._gems[i];
                    if (st.KnownEmpty) { lines.Add($"gem{i + 1}=empty"); }
                    else if (st.Sheet != null) { lines.Add($"gem{i + 1}={st.Sheet}|{st.Index}"); }
                }
                File.WriteAllLines(this.StatePath, lines);
            }
            catch (Exception) { }
        }

        private void LoadState()
        {
            try
            {
                if (!File.Exists(this.StatePath)) { return; }
                foreach (var line in File.ReadAllLines(this.StatePath))
                {
                    var eq = line.IndexOf('=');
                    if (eq <= 0) { continue; }
                    var key = line.Substring(0, eq);
                    var val = line.Substring(eq + 1);

                    if (key == "grid")
                    {
                        // Tolerate files written by an earlier build using a comma.
                        var p = val.Replace(',', '.').Split('|');
                        if (p.Length == 4 &&
                            Single.TryParse(p[0], System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture, out var x) &&
                            Single.TryParse(p[1], System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture, out var y) &&
                            Single.TryParse(p[2], System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture, out var s) &&
                            Single.TryParse(p[3], System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture, out var t))
                        {
                            this._grid = new Grid { X = x, Y0 = y, Size = s, Stride = t };
                        }
                    }
                    else if (key == "gems")
                    {
                        // Absent in files written before the bar length was variable; the
                        // field defaults to the nine-gem run those builds assumed.
                        if (Int32.TryParse(val, out var gc) && gc >= 1 && gc <= MaxGemCount) { this._gemCount = gc; }
                    }
                    else if (key == "iconDir") { this._iconDir = val; }
                    else if (key == "gameDir") { this._gameDir = val; }
                    else if (key.StartsWith("gem"))
                    {
                        if (Int32.TryParse(key.Substring(3), out var n) && n >= 1 && n <= MaxGemCount)
                        {
                            if (val == "empty") { this._gems[n - 1].KnownEmpty = true; continue; }
                            var cut = val.LastIndexOf('|');
                            if (cut > 0 && Int32.TryParse(val.Substring(cut + 1), out var idx))
                            {
                                this._gems[n - 1].Sheet = val.Substring(0, cut);
                                this._gems[n - 1].Index = idx;
                            }
                        }
                    }
                }
            }
            catch (Exception) { }
        }

        // Offline diagnostic: run the real locate pipeline on a saved capture instead of
        // the live window - same code path as Update's expensive branch. This is how a
        // locate failure gets debugged from a screenshot instead of guessed at against
        // a moving game.
        public String LocateFromBitmap(Bitmap bmp)
        {
            lock (this._sync)
            {
                if (!this.EnsureLibrary()) { return "library unavailable"; }
                var screen = FloatImg.FromBitmap(bmp);
                var sw = System.Diagnostics.Stopwatch.StartNew();
                var grid = this.LocateBar(screen);
                sw.Stop();
                return grid == null
                    ? $"NOT FOUND in {sw.Elapsed.TotalSeconds:F1} s"
                    : $"grid x={grid.X:F2} y0={grid.Y0:F2} size={grid.Size:F2} stride={grid.Stride:F2} slots={this._gemCount} in {sw.Elapsed.TotalSeconds:F1} s";
            }
        }

        // Offline diagnostic sibling of LocateFromBitmap: one watch-pass cycle on a saved
        // capture, every per-gem intermediate returned as text.
        public String WatchFromBitmap(Bitmap bmp)
        {
            lock (this._sync)
            {
                if (!this.EnsureLibrary()) { return "library unavailable"; }
                if (this._grid == null) { return "no saved grid"; }
                var margin = 8;
                var strip = FloatImg.FromBitmap(bmp,
                    (Int32)(this._grid.X - margin),
                    (Int32)(this._grid.Y0 - margin),
                    (Int32)(this._grid.Size + 2 * margin),
                    (Int32)((this._gemCount - 1) * this._grid.Stride + this._grid.Size + 2 * margin));
                var scores = this.GemScores(strip, this._grid);
                var sb = new System.Text.StringBuilder();
                sb.AppendLine($"gemCount={this._gemCount} grid x={this._grid.X:F2} y0={this._grid.Y0:F2} size={this._grid.Size:F2} stride={this._grid.Stride:F2}");
                for (var i = 0; i < this._gemCount; i++)
                {
                    var st = this._gems[i];
                    var flat = Single.IsNaN(scores[i]) && st.Norm24 != null;
                    sb.AppendLine($"gem {i + 1}: score={scores[i]:F3} known={(st.Norm24 != null ? 1 : 0)} empty={(st.KnownEmpty ? 1 : 0)} flat={(flat ? 1 : 0)}");
                }
                return sb.ToString();
            }
        }

        // Rebuild in-memory images and descriptors for gems restored from disk.
        public void RestoreImages()
        {
            lock (this._sync)
            {
                if (!this.EnsureLibrary()) { return; }
                var byKey = new Dictionary<String, LibIcon>();
                foreach (var li in this._lib) { byKey[li.Sheet + "|" + li.Index] = li; }

                var known = 0;
                foreach (var st0 in this._gems) { if (st0.Sheet != null) { known++; } }
                var restored = 0;
                for (var i = 0; i < MaxGemCount; i++)
                {
                    var st = this._gems[i];
                    if (st.Sheet == null || st.Png != null) { continue; }
                    if (byKey.TryGetValue(st.Sheet + "|" + st.Index, out var li) && this.ApplyIcon(i, li, st.Score))
                    {
                        restored++;
                    }
                }
                // Without this the keys keep whatever the host drew before: the first
                // read after a reload finds everything already correct, reports
                // NoChange, and nothing ever asks them to repaint.
                this._log?.Info($"RestoreImages: {known} gem(s) in saved state, {restored} rebuilt, library={this._lib?.Count ?? 0} from '{this._iconDir}'");
                if (restored > 0) { this.IconsChanged?.Invoke(this, EventArgs.Empty); }
            }
        }
    }
}
