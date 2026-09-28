import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Coverings.CocycleFaceSheets

set_option autoImplicit false

open Set Topology

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {ι : Type*} [Fintype ι] {A : PreAbstractSimplicialComplex ι}

def sheetCoordinate (c : A.ModTwoEdgeCocycle) (z : c.bundle.TotalSpace) : ZMod 2 := z.snd

def sheetPoint (c : A.ModTwoEdgeCocycle) (x : A.barycentricSpace) (b : ZMod 2) :
    c.bundle.TotalSpace := ⟨x, b⟩

def deckAdd (c : A.ModTwoEdgeCocycle) (b : ZMod 2) (z : c.bundle.TotalSpace) :
    c.bundle.TotalSpace := c.sheetPoint z.proj (c.sheetCoordinate z + b)

theorem continuous_deckAdd (c : A.ModTwoEdgeCocycle) (b : ZMod 2) :
    Continuous (c.deckAdd b) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let T := c.bundle.localTrivAt z.proj
  have hz : z ∈ T.source := c.bundle.mem_baseSet_at z.proj
  have htarget : ∀ᶠ y in 𝓝 z, c.deckAdd b y ∈ T.source :=
    T.open_source.mem_nhds hz
  apply (T.toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left htarget).mpr
  have heq : (T ∘ c.deckAdd b) = fun y => ((T y).1, (T y).2 + b) := by
    funext y
    apply Prod.ext
    · rfl
    · change (c.sheetCoordinate y + b) + c.value (c.bundle.indexAt y.proj)
          (c.bundle.indexAt z.proj) =
        (c.sheetCoordinate y + c.value (c.bundle.indexAt y.proj) (c.bundle.indexAt z.proj)) + b
      abel
  change ContinuousAt (T ∘ c.deckAdd b) z
  rw [heq]
  exact (T.continuousAt hz).fst.prodMk
    (((continuous_of_discreteTopology : Continuous (fun a : ZMod 2 => a + b))).continuousAt.comp
      (T.continuousAt hz).snd)

noncomputable def pathValue (c : A.ModTwoEdgeCocycle)
    {x y : A.barycentricSpace} (p : Path x y) : ZMod 2 :=
  c.sheetCoordinate (c.isCoveringMap.liftPath p.toContinuousMap (c.sheetPoint x 0) p.source 1)

theorem pathValue_of_lift (c : A.ModTwoEdgeCocycle)
    {x y : A.barycentricSpace} (p : Path x y)
    {a b : c.bundle.TotalSpace} (L : Path a b)
    (hL : ∀ t, c.bundle.proj (L t) = p t) :
    c.pathValue p = c.sheetCoordinate b - c.sheetCoordinate a := by
  let M : C(unitInterval, c.bundle.TotalSpace) :=
    ⟨fun t => c.deckAdd (-c.sheetCoordinate a) (L t),
      (c.continuous_deckAdd _).comp L.continuous⟩
  have ha : a.proj = x := by simpa using hL 0
  have hzero : M 0 = c.sheetPoint x 0 := by
    change c.deckAdd (-c.sheetCoordinate a) (L 0) = _
    rw [L.source]
    simp only [deckAdd, add_neg_cancel, ha]
  have heq : M = c.isCoveringMap.liftPath p.toContinuousMap (c.sheetPoint x 0) p.source :=
    (c.isCoveringMap.eq_liftPath_iff' p.source).mpr ⟨funext hL, hzero⟩
  change c.sheetCoordinate
    (c.isCoveringMap.liftPath p.toContinuousMap (c.sheetPoint x 0) p.source 1) = _
  rw [← heq]
  change c.sheetCoordinate (L 1) + -c.sheetCoordinate a = _
  rw [L.target, sub_eq_add_neg]

theorem pathValue_refl (c : A.ModTwoEdgeCocycle) (x : A.barycentricSpace) :
    c.pathValue (Path.refl x) = 0 := by
  simpa only [sub_self] using c.pathValue_of_lift (Path.refl x)
    (Path.refl (c.sheetPoint x 0)) (fun _ => rfl)

theorem pathValue_trans (c : A.ModTwoEdgeCocycle)
    {x y z : A.barycentricSpace} (p : Path x y) (q : Path y z) :
    c.pathValue (p.trans q) = c.pathValue p + c.pathValue q := by
  let L := c.isCoveringMap.liftPath p.toContinuousMap (c.sheetPoint x 0) p.source
  have hL (t) : c.bundle.proj (L t) = p t :=
    congr_fun (c.isCoveringMap.liftPath_lifts p.toContinuousMap (c.sheetPoint x 0) p.source) t
  have hLy : q 0 = c.bundle.proj (L 1) := q.source.trans
    ((hL 1).trans p.target).symm
  let M := c.isCoveringMap.liftPath q.toContinuousMap (L 1) hLy
  have hM (t) : c.bundle.proj (M t) = q t :=
    congr_fun (c.isCoveringMap.liftPath_lifts q.toContinuousMap (L 1) hLy) t
  let LP : Path (c.sheetPoint x 0) (L 1) :=
    ⟨L, c.isCoveringMap.liftPath_zero p.toContinuousMap (c.sheetPoint x 0) p.source, rfl⟩
  let MP : Path (L 1) (M 1) :=
    ⟨M, c.isCoveringMap.liftPath_zero q.toContinuousMap (L 1) hLy, rfl⟩
  have hLM (t) : c.bundle.proj ((LP.trans MP) t) = (p.trans q) t := by
    simp only [Path.trans_apply]
    split_ifs <;> first | exact hL _ | exact hM _
  have htotal := c.pathValue_of_lift (p.trans q) (LP.trans MP) hLM
  change c.pathValue (p.trans q) = c.sheetCoordinate (M 1) - 0 at htotal
  rw [sub_zero] at htotal
  have hq := c.pathValue_of_lift q MP hM
  change c.pathValue (p.trans q) = c.sheetCoordinate (L 1) + c.pathValue q
  exact htotal.trans (by rw [hq]; abel)

theorem pathValue_eq_of_homotopic (c : A.ModTwoEdgeCocycle)
    {x y : A.barycentricSpace} {p q : Path x y} (h : p.Homotopic q) :
    c.pathValue p = c.pathValue q :=
  congrArg c.sheetCoordinate
    (c.isCoveringMap.liftPath_apply_one_eq_of_homotopicRel h
      (c.sheetPoint x 0) p.source q.source)

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle
