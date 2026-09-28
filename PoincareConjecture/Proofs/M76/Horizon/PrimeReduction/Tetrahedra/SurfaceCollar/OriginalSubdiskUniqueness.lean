import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubdiskUniqueness
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedInverse
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem original_subdisk_images_eq_of_same_rim
    {X E F G ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {D r : Set E} {A a : Set F} {B b : Set G}
    (hD : IsFinitePLBallPair P2 D r)
    (hA : IsFinitePLBallPair P2 A a) (hB : IsFinitePLBallPair P2 B b)
    {f : E → X} {p : F → X} {q : G → X}
    (hf : PolyhedralPLInCharts e f D) (hfi : InjOn f D)
    (hp : PolyhedralPLInCharts e p A) (hpi : InjOn p A)
    (hq : PolyhedralPLInCharts e q B) (hqi : InjOn q B)
    (hpD : p '' A ⊆ f '' D) (hqD : q '' B ⊆ f '' D)
    (hrim : p '' a = q '' b) : p '' A = q '' B := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  have hfe : Topology.IsEmbedding (fun x : D => f x) :=
    (hf.continuousOn.domRestrict.isClosedEmbedding
      (fun x y h => Subtype.ext (hfi x.property y.property h))).isEmbedding
  obtain ⟨k,hkc,hleft,hright,hkD⟩ := hfe.exists_inverse_on_image
  have hkp : MapsTo (k ∘ p) A D := fun x hx => hkD (hpD ⟨x,hx,rfl⟩)
  have hkq : MapsTo (k ∘ q) B D := fun x hx => hkD (hqD ⟨x,hx,rfl⟩)
  have hpk (x : F) (hx : x ∈ A) : f (k (p x)) = p x := hright _ (hpD ⟨x,hx,rfl⟩)
  have hqk (x : G) (hx : x ∈ B) : f (k (q x)) = q x := hright _ (hqD ⟨x,hx,rfl⟩)
  have hkpPL : FinitePiecewiseAffineOn (k ∘ p) A := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKA,_⟩,_⟩,_⟩ := hA
    rw [←hKA]
    apply hf.finitePiecewiseAffineOn_lift he hfi K hK
      ((hkc.comp hp.continuousOn (fun x hx => hpD ⟨x,hx,rfl⟩)).mono hKA.subset)
      (hkp.mono_left hKA.subset)
    exact (hp.restrict_finite K hK hKA.subset).congr (fun x hx => (hpk x (hKA.subset hx)).symm)
  have hkqPL : FinitePiecewiseAffineOn (k ∘ q) B := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKB,_⟩,_⟩,_⟩ := hB
    rw [←hKB]
    apply hf.finitePiecewiseAffineOn_lift he hfi K hK
      ((hkc.comp hq.continuousOn (fun x hx => hqD ⟨x,hx,rfl⟩)).mono hKB.subset)
      (hkq.mono_left hKB.subset)
    exact (hq.restrict_finite K hK hKB.subset).congr (fun x hx => (hqk x (hKB.subset hx)).symm)
  have hkpi : InjOn (k ∘ p) A := by
    intro x hx y hy hxy
    exact hpi hx hy ((hpk x hx).symm.trans ((congrArg f hxy).trans (hpk y hy)))
  have hkqi : InjOn (k ∘ q) B := by
    intro x hx y hy hxy
    exact hqi hx hy ((hqk x hx).symm.trans ((congrArg f hxy).trans (hqk y hy)))
  have hmark : (k ∘ p) '' a = (k ∘ q) '' b := by rw [image_comp,image_comp,hrim]
  have hAB := hD.subdisks_eq_of_same_rim (hA.image hkpPL hkpi)
    (hmark.symm ▸ hB.image hkqPL hkqi) (image_subset_iff.mpr hkp) (image_subset_iff.mpr hkq)
  have hpinv : f '' ((k ∘ p) '' A) = p '' A := by
    rw [←image_comp]
    exact image_congr hpk
  have hqinv : f '' ((k ∘ q) '' B) = q '' B := by
    rw [←image_comp]
    exact image_congr hqk
  rw [←hpinv,←hqinv,hAB]

end PoincareConjecture.M76
