import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.Mathlib.RelativeChartRestriction
import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Coordinates.LocalPairChartCoordinates

/-!
# Relative pair products with the original normal coordinate

Restrict the original region chart to its actual tangential subspace,
then use its complete zero slice as the common base. The auxiliary
product chart is topological; its normal coordinate is literally the
one in the original chart. See rigidity derivation013, section2.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76

/-- A genuine tangential-subspace pair model gives a local product
on the original region. This includes a boundary half-plane without
replacing it by an open Euclidean plane. See rigidity013, section2. -/
theorem exists_relative_pair_product_with_normal
    {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]
    (H : OpenPartialHomeomorph X (P × ℝ)) {R S : Set X} (T : Set P)
    (hregion : ∀ y ∈ H.source, y ∈ R ↔ (H y).1 ∈ T)
    (hdisk : ∀ y ∈ H.source, y ∈ S ↔ (H y).1 ∈ T ∧ (H y).2 = 0)
    (x : (Subtype.val : R → X) ⁻¹' S) (hx : ((x : R) : X) ∈ H.source) :
    ∃ q : OpenPartialHomeomorph (((Subtype.val : R → X) ⁻¹' S) × ℝ) R,
      (x, (0 : ℝ)) ∈ q.source ∧
      q.target ⊆ (Subtype.val : R → X) ⁻¹' H.source ∧
      (∀ s, (s, (0 : ℝ)) ∈ q.source → q (s, 0) = (s : R)) ∧
      (∀ z ∈ q.source, (H (q z : X)).2 = z.2) ∧
      ∀ z ∈ q.source, (q z : X) ∈ S ↔ z.2 = 0 := by
  have himage : H.IsImage R (T ×ˢ (univ : Set ℝ)) := by
    intro y hy
    exact ⟨fun ht => (hregion y hy).mpr ht.1,
      fun hR => ⟨(hregion y hy).mp hR, mem_univ _⟩⟩
  obtain ⟨r, hrS, _, hrval, _⟩ := himage.exists_subtype_chart (x : R) hx
  let c : (T ×ˢ (univ : Set ℝ)) ≃ₜ (T × ℝ) :=
    (Homeomorph.Set.prod T (univ : Set ℝ)).trans
      ((Homeomorph.refl T).prodCongr (Homeomorph.Set.univ ℝ))
  let f := r.transHomeomorph c
  have hnormal (y : R) (hy : y ∈ f.source) : (f y).2 = (H (y : X)).2 := by
    change (r y : P × ℝ).2 = (H (y : X)).2
    exact congrArg Prod.snd (hrval y hy)
  have hsource (y : R) (hy : y ∈ f.source) : (y : X) ∈ H.source := by
    change y ∈ (Subtype.val : R → X) ⁻¹' H.source
    rw [← hrS]
    exact hy
  let S' : Set R := (Subtype.val : R → X) ⁻¹' S
  have hpair : ∀ y ∈ f.source, y ∈ S' ↔ (f y).2 = 0 := by
    intro y hy
    change (y : X) ∈ S ↔ (f y).2 = 0
    rw [hnormal y hy]
    have hT : (H (y : X)).1 ∈ T := (hregion y (hsource y hy)).mp y.property
    exact (hdisk y (hsource y hy)).trans
      ⟨And.right, fun hz => ⟨hT, hz⟩⟩
  have hxf : (x : R) ∈ f.source := by
    change (x : R) ∈ r.source
    rw [hrS]
    exact hx
  obtain ⟨q, hxq, hqf, hqbase, hqnormal⟩ :=
    BrownCollar.exists_local_pair_chart_with_normal f S' hpair x hxf
  refine ⟨q, hxq, ?_, hqbase, ?_, ?_⟩
  · exact fun y hy => hsource y (hqf hy)
  · intro z hz
    exact (hnormal (q z) (hqf (q.map_source hz))).symm.trans (hqnormal z hz)
  · intro z hz
    change q z ∈ S' ↔ z.2 = 0
    rw [hpair (q z) (hqf (q.map_source hz)), hqnormal z hz]

end PoincareMT.M76
