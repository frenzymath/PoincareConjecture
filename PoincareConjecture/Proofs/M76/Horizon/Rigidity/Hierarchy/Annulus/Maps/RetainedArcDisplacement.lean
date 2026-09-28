import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.OriginalCircleCoordinate
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.Translations.Vector
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Affine.Mathlib.ContinuousAffineSelection
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.LocalPLScalarArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPLProduct
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc










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

theorem exists_hamiltonZero_retained_arc_displacement
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (heR : PLDomain e R) {cut alpha beta : ℝ}
    (halpha : cut < alpha) (hab : alpha ≤ beta) (hbeta : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (W : C(X0, V3))
    (hWPL : ∀ i, LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target)
    (hW1 : ∀ x, W x 1 = 0) (hWzero : ∀ x ∉ interior R, W x = 0) :
    let n := (AddCircle.openPartialHomeomorphCoe p cut).symm ∘ hamiltonZeroCircleMap phi
    ∃ V : C(X0, V3),
      (∀ i, LocallyPiecewiseAffineOn (V ∘ (e i).symm) (e i).target) ∧
      (∀ x, V x 0 = W x 0) ∧ (∀ x, V x 1 = 0) ∧
      (∀ x ∈ R, V x 2 = max alpha (min beta (n x + W x 2)) - n x) ∧
      (∀ x ∉ interior R, V x = 0) ∧ (∀ x, W x = 0 → V x = 0) ∧
      (∀ x ∈ R, n x + W x 2 ∈ Icc alpha beta → V x = W x) ∧
      ∀ x ∈ R, ∀ t : unitInterval,
        (Q0 (hamiltonZeroTargetVectorTranslation
          ((t : ℝ) • V x, hamiltonZeroAmbientMap phi x))).2 ∈
            AddCircle.closedIntervalArc p alpha beta := by
  classical
  intro n
  let J := AddCircle.openPartialHomeomorphCoe p cut
  let U := hamiltonZeroCircleMap phi ⁻¹' J.target
  have hU : IsOpen U := J.open_target.preimage (hamiltonZeroCircleMap phi).continuous
  have hsource (s : ℝ) (hs : s ∈ Icc alpha beta) : s ∈ J.source :=
    ⟨halpha.trans_le hs.1, hs.2.trans_lt hbeta⟩
  have hn (x : X0) (hx : x ∈ R) :
      n x ∈ Icc alpha beta ∧ ((n x : ℝ) : C0) = hamiltonZeroCircleMap phi x := by
    obtain ⟨s, hs, hsq⟩ := hR hx
    have heq : n x = s := by
      change J.symm (hamiltonZeroCircleMap phi x) = s
      rw [← hsq]
      exact J.left_inv (hsource s hs)
    rw [heq]
    exact ⟨hs, hsq⟩
  have hRU : R ⊆ U := by
    intro x hx
    change hamiltonZeroCircleMap phi x ∈ J.target
    rw [show hamiltonZeroCircleMap phi x = ((n x : ℝ) : C0) from (hn x hx).2.symm]
    exact J.map_source (hsource (n x) (hn x hx).1)
  have hnc : ContinuousOn n U := J.continuousOn_symm.comp
    (hamiltonZeroCircleMap phi).continuous.continuousOn (fun _ hx => hx)
  let k : X0 → ℝ := fun x => max alpha (min beta (n x + W x 2)) - n x
  have hkR : ContinuousOn k R :=
    (continuousOn_const.sup (continuousOn_const.inf
      ((hnc.mono hRU).add ((continuous_apply 2).comp W.continuous).continuousOn))).sub
      (hnc.mono hRU)
  have hkzero (x : X0) (hx : x ∈ R) (hWx : W x = 0) : k x = 0 := by
    dsimp only [k]
    rw [hWx]
    simp only [Pi.zero_apply, add_zero, min_eq_right (hn x hx).1.2,
      max_eq_right (hn x hx).1.1, sub_self]
  have hkfront (x : X0) (hx : x ∈ frontier R) : k x = 0 :=
    hkzero x (heR.closed.frontier_subset hx) (hWzero x hx.2)
  let v : C(X0, ℝ) := ⟨R.piecewise k (fun _ => 0), continuous_piecewise hkfront
    (by simpa only [heR.closed.closure_eq] using hkR) continuousOn_const⟩
  have hvR (x : X0) (hx : x ∈ R) : v x = k x := piecewise_eq_of_mem R k (fun _ => 0) hx
  have hvout (x : X0) (hx : x ∉ R) : v x = 0 := piecewise_eq_of_notMem R k (fun _ => 0) hx
  have hvselect (x : X0) : v x = 0 ∨ v x = k x := by
    by_cases hx : x ∈ R
    · exact Or.inr (hvR x hx)
    · exact Or.inl (hvout x hx)
  have hWcoord (i : ι) (a : Fin 3) :
      LocallyPiecewiseAffineOn (fun z => W ((e i).symm z) a) (e i).target := by
    have h := (locallyPiecewiseAffineOn_affine
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) a).toContinuousAffineMap
      isOpen_univ).comp (hWPL i)
    rw [preimage_univ, inter_univ] at h
    exact h.congr (fun _ _ => rfl)
  have hvPL (i : ι) : LocallyPiecewiseAffineOn (v ∘ (e i).symm) (e i).target := by
    let B := (e i).target ∩ (e i).symm ⁻¹' U
    have hB : IsOpen B := (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hU
    have hnPL : LocallyPiecewiseAffineOn (n ∘ (e i).symm) B :=
      hphi.locallyPL_hamiltonZero_circle_coordinate hd cut i
    have hkPL : LocallyPiecewiseAffineOn (k ∘ (e i).symm) B := by
      have haPL := locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 alpha) hB
      have hbPL := locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 beta) hB
      exact ((haPL.max (hbPL.min (hnPL.add ((hWcoord i 2).mono hB inter_subset_left)))).add
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
  let V : C(X0, V3) := ⟨fun x => ![W x 0, W x 1, v x], by
    apply continuous_pi
    intro a
    fin_cases a
    · change Continuous (fun x => W x 0)
      exact (continuous_apply 0).comp W.continuous
    · change Continuous (fun x => W x 1)
      exact (continuous_apply 1).comp W.continuous
    · exact v.continuous⟩
  have hVzero (x : X0) (hx : W x = 0) : V x = 0 := by
    have hvx : v x = 0 := by
      by_cases hxR : x ∈ R
      · rw [hvR x hxR, hkzero x hxR hx]
      · exact hvout x hxR
    change ![W x 0, W x 1, v x] = 0
    rw [hx, hvx]
    ext a
    fin_cases a <;> rfl
  refine ⟨V, ?_, fun _ => rfl, hW1, ?_, fun x hx => hVzero x (hWzero x hx), hVzero, ?_, ?_⟩
  · intro i
    apply LocallyPiecewiseAffineOn.pi (e i).open_target
    intro a
    fin_cases a
    · exact hWcoord i 0
    · exact hWcoord i 1
    · exact hvPL i
  · intro x hx
    exact hvR x hx
  · intro x hx hbound
    have hvx : v x = W x 2 := by
      rw [hvR x hx]
      dsimp only [k]
      rw [min_eq_right hbound.2, max_eq_right hbound.1]
      ring
    ext a
    fin_cases a
    · rfl
    · rfl
    · exact hvx
  · intro x hx t
    rw [hamiltonZeroTargetVectorTranslation_coordinates]
    change (Q0 (hamiltonZeroAmbientMap phi x)).2 + (((t : ℝ) * v x : ℝ) : C0) ∈ _
    have hnormal : (Q0 (hamiltonZeroAmbientMap phi x)).2 = (n x : C0) := (hn x hx).2.symm
    rw [hnormal, ← AddCircle.coe_add]
    refine ⟨n x + (t : ℝ) * v x, ?_, rfl⟩
    rw [hvR x hx]
    have hc : max alpha (min beta (n x + W x 2)) ∈ Icc alpha beta :=
      ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
    have hh := (convex_Icc alpha beta) (hn x hx).1 hc
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
    convert hh using 1
    dsimp only [k]
    ring

end PoincareConjecture.M76
