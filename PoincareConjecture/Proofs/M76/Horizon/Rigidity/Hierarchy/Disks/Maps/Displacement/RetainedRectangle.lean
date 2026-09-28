import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.Displacement.Extension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.RetainedArcDisplacement

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

private theorem local_scalar_selection_zero {f g : V3 → ℝ} {U : Set V3}
    (hf : LocallyPiecewiseAffineOn f U) (hg : ContinuousOn g U)
    (hselect : ∀ x ∈ U, g x = 0 ∨ g x = f x) : LocallyPiecewiseAffineOn g U := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  obtain ⟨L, hL, hLK, hgL⟩ := (hfK.finitePiecewiseAffineOn hK).continuous_selection_zero
    (hg.mono hKU) (fun y hy => hselect y (hKU hy))
  exact ⟨L, hL, hLK.symm ▸ hxK, hLK ▸ hKU, hgL⟩

private theorem exists_retained_circle_scalar_displacement
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    {R : Set X0} (heR : PLDomain e R) (q : C(X0, C0))
    {cut a b : ℝ} (ha : cut < a) (hab : a ≤ b) (hb : b < cut + p)
    (hR : R ⊆ q ⁻¹' AddCircle.closedIntervalArc p a b)
    (hlocal : ∀ i, let A := AddCircle.openPartialHomeomorphCoe p cut
      LocallyPiecewiseAffineOn ((A.symm ∘ q) ∘ (e i).symm)
        ((e i).target ∩ (e i).symm ⁻¹' (q ⁻¹' A.target)))
    (w : C(X0, ℝ))
    (hw : ∀ i, LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target)
    (hwzero : ∀ x ∉ interior R, w x = 0) :
    let n := (AddCircle.openPartialHomeomorphCoe p cut).symm ∘ q
    ∃ v : C(X0, ℝ),
      (∀ i, LocallyPiecewiseAffineOn (v ∘ (e i).symm) (e i).target) ∧
      (∀ x ∉ interior R, v x = 0) ∧ (∀ x, w x = 0 → v x = 0) ∧
      (∀ x ∈ R, n x + w x ∈ Icc a b → v x = w x) ∧
      ∀ x ∈ R, ∀ t : unitInterval, q x + (((t : ℝ) * v x : ℝ) : C0) ∈
        AddCircle.closedIntervalArc p a b := by
  classical
  intro n
  let J := AddCircle.openPartialHomeomorphCoe p cut
  let U := q ⁻¹' J.target
  have hU : IsOpen U := J.open_target.preimage q.continuous
  have hsource (s : ℝ) (hs : s ∈ Icc a b) : s ∈ J.source :=
    ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have hn (x : X0) (hx : x ∈ R) : n x ∈ Icc a b ∧ ((n x : ℝ) : C0) = q x := by
    obtain ⟨s, hs, hsq⟩ := hR hx
    have heq : n x = s := by
      change J.symm (q x) = s
      rw [← hsq]
      exact J.left_inv (hsource s hs)
    rw [heq]
    exact ⟨hs, hsq⟩
  have hRU : R ⊆ U := by
    intro x hx
    change q x ∈ J.target
    rw [← (hn x hx).2]
    exact J.map_source (hsource (n x) (hn x hx).1)
  have hnc : ContinuousOn n U := J.continuousOn_symm.comp
    q.continuous.continuousOn (fun _ hx => hx)
  let k : X0 → ℝ := fun x => max a (min b (n x + w x)) - n x
  have hkR : ContinuousOn k R :=
    (continuousOn_const.sup (continuousOn_const.inf
      ((hnc.mono hRU).add w.continuous.continuousOn))).sub (hnc.mono hRU)
  have hkzero (x : X0) (hx : x ∈ R) (hwx : w x = 0) : k x = 0 := by
    dsimp only [k]
    rw [hwx]
    simp only [add_zero, min_eq_right (hn x hx).1.2, max_eq_right (hn x hx).1.1, sub_self]
  have hkfront (x : X0) (hx : x ∈ frontier R) : k x = 0 :=
    hkzero x (heR.closed.frontier_subset hx) (hwzero x hx.2)
  let v : C(X0, ℝ) := ⟨R.piecewise k (fun _ => 0), continuous_piecewise hkfront
    (by simpa only [heR.closed.closure_eq] using hkR) continuousOn_const⟩
  have hvR (x : X0) (hx : x ∈ R) : v x = k x := piecewise_eq_of_mem R k (fun _ => 0) hx
  have hvout (x : X0) (hx : x ∉ R) : v x = 0 := piecewise_eq_of_notMem R k (fun _ => 0) hx
  have hvzero (x : X0) (hx : w x = 0) : v x = 0 := by
    by_cases hxR : x ∈ R
    · rw [hvR x hxR, hkzero x hxR hx]
    · exact hvout x hxR
  have hvselect (x : X0) : v x = 0 ∨ v x = k x := by
    by_cases hx : x ∈ R
    · exact Or.inr (hvR x hx)
    · exact Or.inl (hvout x hx)
  refine ⟨v, ?_, fun x hx => hvzero x (hwzero x hx), hvzero, ?_, ?_⟩
  · intro i
    let B := (e i).target ∩ (e i).symm ⁻¹' U
    have hB : IsOpen B := (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hU
    have hnPL : LocallyPiecewiseAffineOn (n ∘ (e i).symm) B := hlocal i
    have hkPL : LocallyPiecewiseAffineOn (k ∘ (e i).symm) B := by
      have haPL := locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 a) hB
      have hbPL := locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 b) hB
      exact ((haPL.max (hbPL.min (hnPL.add ((hw i).mono hB inter_subset_left)))).add
        hnPL.neg).congr (fun _ _ => by dsimp [k]; ring)
    have hvB := local_scalar_selection_zero hkPL
      ((v.continuous.comp_continuousOn (e i).continuousOn_symm).mono inter_subset_left)
      (fun z _ => hvselect ((e i).symm z))
    apply LocallyPiecewiseAffineOn.locality
    intro z hz
    by_cases hxR : (e i).symm z ∈ R
    · exact ⟨B, ⟨hz, hRU hxR⟩, hvB.mono ((e i).open_target.inter hB) inter_subset_right⟩
    · let O := (e i).target ∩ (e i).symm ⁻¹' Rᶜ
      have hO : IsOpen O := (e i).symm.continuousOn.isOpen_inter_preimage
        (e i).open_target heR.closed.isOpen_compl
      have hzeroPL : LocallyPiecewiseAffineOn (v ∘ (e i).symm) O :=
        (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 (0 : ℝ)) hO).congr
          (fun y hy => (hvout _ hy.2).symm)
      exact ⟨O, ⟨hz, hxR⟩, hzeroPL.mono ((e i).open_target.inter hO) inter_subset_right⟩
  · intro x hx hbound
    rw [hvR x hx]
    dsimp only [k]
    rw [min_eq_right hbound.2, max_eq_right hbound.1]
    ring
  · intro x hx t
    rw [← (hn x hx).2, ← AddCircle.coe_add]
    refine ⟨n x + (t : ℝ) * v x, ?_, rfl⟩
    rw [hvR x hx]
    have hc : max a (min b (n x + w x)) ∈ Icc a b :=
      ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
    have hh := (convex_Icc a b) (hn x hx).1 hc
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
    convert hh using 1
    dsimp only [k]
    ring

theorem exists_hamiltonZero_retained_rectangle_displacement
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (heR : PLDomain e R) {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hab : alpha ≤ beta) (hbeta : beta < cut + p)
    (ha : cut' < a) (horder : a ≤ b) (hb : b < cut' + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (W : C(X0, V3))
    (hWPL : ∀ i, LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target)
    (hW0 : ∀ x, W x 0 = 0) (hWzero : ∀ x ∉ interior R, W x = 0) :
    let n := (AddCircle.openPartialHomeomorphCoe p cut).symm ∘ hamiltonZeroCircleMap phi
    let m := (AddCircle.openPartialHomeomorphCoe p cut').symm ∘ hamiltonZeroSecondCircleMap phi
    ∃ V : C(X0, V3),
      (∀ i, LocallyPiecewiseAffineOn (V ∘ (e i).symm) (e i).target) ∧
      (∀ x, V x 0 = 0) ∧ (∀ x ∉ interior R, V x = 0) ∧
      (∀ x, W x = 0 → V x = 0) ∧
      (∀ x ∈ R, n x + W x 2 ∈ Icc alpha beta → m x + W x 1 ∈ Icc a b → V x = W x) ∧
      ∀ x ∈ R, ∀ t : unitInterval,
        (Q0 (hamiltonZeroTargetVectorTranslation
          ((t : ℝ) • V x, hamiltonZeroAmbientMap phi x))).2 ∈
            AddCircle.closedIntervalArc p alpha beta ∧
        (Q0 (hamiltonZeroTargetVectorTranslation
          ((t : ℝ) • V x, hamiltonZeroAmbientMap phi x))).1.2 ∈
            AddCircle.closedIntervalArc p a b := by
  intro n m
  let coord (k : Fin 3) : C(X0, ℝ) := ⟨fun x => W x k, (continuous_apply k).comp W.continuous⟩
  have hcoord (k : Fin 3) (i : ι) :
      LocallyPiecewiseAffineOn ((coord k) ∘ (e i).symm) (e i).target := by
    have h := (locallyPiecewiseAffineOn_affine
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) k).toContinuousAffineMap
      isOpen_univ).comp (hWPL i)
    rw [preimage_univ, inter_univ] at h
    exact h.congr (fun _ _ => rfl)
  obtain ⟨v, hv, hvzero, hvzero', hvsame, hvarc⟩ := exists_retained_circle_scalar_displacement
    e heR (hamiltonZeroCircleMap phi) halpha hab hbeta hfirst
    (fun i => hphi.locallyPL_hamiltonZero_circle_coordinate hd cut i)
    (coord 2) (hcoord 2) (fun x hx => congrFun (hWzero x hx) 2)
  obtain ⟨w, hw, hwzero, hwzero', hwsame, hwarc⟩ := exists_retained_circle_scalar_displacement
    e heR (hamiltonZeroSecondCircleMap phi) ha horder hb hsecond
    (fun i => locallyPL_hamiltonZero_second_circle_coordinate e d hd phi hphi cut' i)
    (coord 1) (hcoord 1) (fun x hx => congrFun (hWzero x hx) 1)
  let V : C(X0, V3) := ⟨fun x => ![0, w x, v x], by
    apply continuous_pi
    intro k
    fin_cases k
    · exact continuous_const
    · exact w.continuous
    · exact v.continuous⟩
  refine ⟨V, ?_, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro i
    apply LocallyPiecewiseAffineOn.pi (e i).open_target
    intro k
    fin_cases k
    · exact locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 (0 : ℝ)) (e i).open_target
    · exact hw i
    · exact hv i
  · intro x hx
    change ![0, w x, v x] = 0
    rw [hwzero x hx, hvzero x hx]
    ext k
    fin_cases k <;> rfl
  · intro x hx
    change ![0, w x, v x] = 0
    rw [hwzero' x (congrFun hx 1), hvzero' x (congrFun hx 2)]
    ext k
    fin_cases k <;> rfl
  · intro x hx hfirstBound hsecondBound
    change ![0, w x, v x] = W x
    rw [hwsame x hx hsecondBound, hvsame x hx hfirstBound]
    ext k
    fin_cases k
    · exact (hW0 x).symm
    · rfl
    · rfl
  · intro x hx t
    rw [hamiltonZeroTargetVectorTranslation_coordinates]
    exact ⟨hvarc x hx t, hwarc x hx t⟩

end PoincareConjecture.M76
