import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FiniteAffineSlope
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.LocallyPiecewiseAffineInverse

/-!
# Explicit local PL height shears

One common affine slope gives mutually inverse local
shears on their exact retained source and target. The
resulting PL coordinate map identifies the original height
with one affine functional. No invariance-of-domain theorem
or boundary regularity is assumed. See Hamilton 1976,
Lemma 2, pp. 64--66, Hudson 1969, pp. 15--19 and derivation 270.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry

/-- A scalar PL height gives a PL displacement by that
height minus a fixed affine coordinate, along one fixed
direction. The parameter is constant over the source.
See Hudson pp. 15--19 and M76 derivation 270. -/
theorem LocallyPiecewiseAffineOn.height_shear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {U : Set E} (hf : LocallyPiecewiseAffineOn f U)
    (ell : E →ᴬ[ℝ] ℝ) (w : E) (c : ℝ) :
    LocallyPiecewiseAffineOn (fun y => (c * (f y - ell y)) • w + y) U := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  refine ⟨K, hK, hxK, hKU, ?_⟩
  intro s hs
  obtain ⟨a, ha⟩ := hfK s hs
  let L := ((ContinuousLinearMap.id ℝ ℝ).smulRight w).toContinuousAffineMap
  refine ⟨L.comp (c • (a - ell)) + ContinuousAffineMap.id ℝ E, ?_⟩
  intro y hy
  change (c * (f y - ell y)) • w + y = (c * (a y - ell y)) • w + y
  rw [ha hy]

end Geometry

namespace OpenPartialHomeomorph

/-- Finite local affine formulas with one common slope
supply an actual PL height coordinate near each point.
Both inverse identities hold on the exact open source and
target, which are restricted before either identity is used.
See Hamilton Lemma 2 and M76 derivation 270. -/
theorem exists_finite_affine_height_shear
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    {f : E → ℝ} {B : Set E} (hf : LocallyPiecewiseAffineOn f B)
    (hB : Convex ℝ B) (A : ι → E →ᴬ[ℝ] ℝ) (w : E)
    (hA : ∀ i, (A i).contLinear w = 1)
    (hselect : ∀ y ∈ B, ∃ i, f y = A i y)
    (ell : E →ᴬ[ℝ] ℝ) (hell : ell.contLinear w = 1)
    {x : E} (hx : x ∈ B) (hxheight : f x = ell x) :
    ∃ H : OpenPartialHomeomorph E E,
      x ∈ H.source ∧ H x = x ∧ H.source ⊆ B ∧ H.target ⊆ B ∧
      H ∈ piecewiseAffineGroupoid E ∧
      ((H : E → E) = fun y => (f y - ell y) • w + y) ∧
      ((H.symm : E → E) = fun y => -(f y - ell y) • w + y) ∧
      ∀ y ∈ H.source, ell (H y) = f y := by
  let F : E → E := fun y => (f y - ell y) • w + y
  let G : E → E := fun y => -(f y - ell y) • w + y
  have hFPL : LocallyPiecewiseAffineOn F B := by
    simpa only [one_mul] using hf.height_shear ell w 1
  have hGPL : LocallyPiecewiseAffineOn G B := by
    simpa only [neg_one_mul] using hf.height_shear ell w (-1)
  let U : Set E := B ∩ F ⁻¹' B
  let V : Set E := B ∩ G ⁻¹' B
  have hU : IsOpen U := hFPL.continuousOn.isOpen_inter_preimage hf.isOpen hf.isOpen
  have hV : IsOpen V := hGPL.continuousOn.isOpen_inter_preimage hf.isOpen hf.isOpen
  have hdiff {y : E} {t : ℝ} (hy : y ∈ B) (hyt : t • w + y ∈ B) :
      f (t • w + y) - ell (t • w + y) = f y - ell y := by
    rw [hf.continuousOn.add_smul_eq_of_finite_affine_selection hB A w hA hselect hy hyt]
    change f y + t - ell (t • w +ᵥ y) = f y - ell y
    rw [ContinuousAffineMap.map_vadd, map_smul, hell]
    change f y + t - (t * 1 + ell y) = f y - ell y
    ring
  have hleft : LeftInvOn G F U := by
    intro y hy
    have hd := hdiff hy.1 hy.2
    change -(f (F y) - ell (F y)) • w + F y = y
    rw [hd]
    change -(f y - ell y) • w + ((f y - ell y) • w + y) = y
    rw [neg_smul, neg_add_cancel_left]
  have hright : LeftInvOn F G V := by
    intro y hy
    have hd := hdiff hy.1 hy.2
    change (f (G y) - ell (G y)) • w + G y = y
    rw [hd]
    change (f y - ell y) • w + (-(f y - ell y) • w + y) = y
    rw [neg_smul, add_neg_cancel_left]
  have hmap : MapsTo F U V := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    change G (F y) ∈ B
    rw [hleft hy]
    exact hy.1
  have hinvmap : MapsTo G V U := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    change F (G y) ∈ B
    rw [hright hy]
    exact hy.1
  let H : OpenPartialHomeomorph E E :=
    { toFun := F
      invFun := G
      source := U
      target := V
      map_source' := hmap
      map_target' := hinvmap
      left_inv' := hleft
      right_inv' := hright
      continuousOn_toFun := hFPL.continuousOn.mono inter_subset_left
      continuousOn_invFun := hGPL.continuousOn.mono inter_subset_left
      open_source := hU
      open_target := hV }
  have hFx : F x = x := by simp [F, hxheight]
  have hxU : x ∈ U := by
    refine ⟨hx, ?_⟩
    change F x ∈ B
    rw [hFx]
    exact hx
  refine ⟨H, hxU, hFx, inter_subset_left, inter_subset_left,
    ?_, rfl, rfl, ?_⟩
  · exact (mem_piecewiseAffineGroupoid_iff_forward H).mpr (hFPL.mono hU inter_subset_left)
  · intro y _
    change ell ((f y - ell y) • w +ᵥ y) = f y
    rw [ContinuousAffineMap.map_vadd, map_smul, hell]
    change (f y - ell y) * 1 + ell y = f y
    ring

end OpenPartialHomeomorph
