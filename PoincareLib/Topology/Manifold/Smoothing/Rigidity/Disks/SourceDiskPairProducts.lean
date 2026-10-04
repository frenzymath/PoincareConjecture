import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.SourceDiskPairCharts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.RelativePairProduct

/-!
# Local normal products on the complete original disk parameter

The actual disk embedding identifies its image in the region with the
original square. Conjugating the relative pair product retains that
whole parameter and the original PL chart's literal normal coordinate.
See rigidity derivation013, section2.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

/-- Every original proper-disk point has an actual local product on
the same complete disk parameter. Its normal value is the original
PL chart value, while no PL assertion about the auxiliary product
chart is made. See rigidity013, section2. -/
theorem exists_original_proper_disk_pair_product
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) {j : V2 → X}
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    (z : D) :
    ∃ (H : OpenPartialHomeomorph X C3) (q : OpenPartialHomeomorph (D × ℝ) R),
      j z ∈ H.source ∧ H (j z) = 0 ∧
      (∀ i,
        LocallyPiecewiseAffineOn ((e i).symm.trans H) ((e i).symm.trans H).source ∧
        LocallyPiecewiseAffineOn (H.symm.trans (e i)) (H.symm.trans (e i)).source) ∧
      (z, (0 : ℝ)) ∈ q.source ∧
      q.target ⊆ (Subtype.val : R → X) ⁻¹' H.source ∧
      (∀ s, (s, (0 : ℝ)) ∈ q.source → (q (s, 0) : X) = j s) ∧
      (∀ w ∈ q.source, (H (q w : X)).2 = w.2) ∧
      ∀ w ∈ q.source, (q w : X) ∈ j '' D ↔ w.2 = 0 := by
  obtain ⟨H, hzH, _, hHz, hHcompat, hmodel⟩ :=
    exists_original_proper_disk_pair_chart he hj hemb hDR hproper z
  let S : Set R := (Subtype.val : R → X) ⁻¹' (j '' D)
  let f : D → S := fun a => ⟨⟨j a, hDR a.property⟩, ⟨a, a.property, rfl⟩⟩
  have hf : Topology.IsEmbedding f := by
    have hval : Topology.IsEmbedding (fun y : S => ((y : R) : X)) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact hval.of_comp_iff.mp hemb
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, ha, hay⟩ := y.property
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hay
  let b : D ≃ₜ S := hf.toHomeomorphOfSurjective hsurj
  have hb (a : D) : ((b a : R) : X) = j a := rfl
  have hbx : ((b z : R) : X) ∈ H.source := by rw [hb]; exact hzH
  obtain ⟨q0, hzq0, hq0H, hq00, hq0normal, hq0pair⟩ :
      ∃ q0 : OpenPartialHomeomorph (S × ℝ) R,
        (b z, (0 : ℝ)) ∈ q0.source ∧
        q0.target ⊆ (Subtype.val : R → X) ⁻¹' H.source ∧
        (∀ s, (s, (0 : ℝ)) ∈ q0.source → q0 (s, 0) = (s : R)) ∧
        (∀ w ∈ q0.source, (H (q0 w : X)).2 = w.2) ∧
        ∀ w ∈ q0.source, (q0 w : X) ∈ j '' D ↔ w.2 = 0 := by
    rcases hmodel with ⟨hinside, hplane⟩ | ⟨hregion, hhalfplane⟩
    · apply exists_relative_pair_product_with_normal H (univ : Set (ℝ × ℝ))
        ?_ ?_ (b z) hbx
      · intro x hx
        exact ⟨fun _ => mem_univ _, fun _ => interior_subset (hinside hx)⟩
      · intro x hx
        exact (hplane x hx).trans ⟨fun h => ⟨mem_univ _, h⟩, And.right⟩
    · exact exists_relative_pair_product_with_normal H {p : ℝ × ℝ | 0 ≤ p.1}
        hregion hhalfplane (b z) hbx
  let p := b.prodCongr (Homeomorph.refl ℝ)
  let q := p.toOpenPartialHomeomorph.trans q0
  refine ⟨H, q, hzH, hHz, hHcompat, ⟨mem_univ _, hzq0⟩, ?_, ?_, ?_, ?_⟩
  · exact fun y hy => hq0H hy.1
  · intro a ha
    change (q0 (b a, (0 : ℝ)) : X) = j a
    rw [hq00 (b a) ha.2]
    exact hb a
  · intro w hw
    exact hq0normal (p w) hw.2
  · intro w hw
    exact hq0pair (p w) hw.2

end PoincareMT.M76
