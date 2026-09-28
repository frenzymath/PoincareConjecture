import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.UnionDisk.Map
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSmallDiskProduct
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem exists_original_finite_proper_disk_product
    {X ι E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R O : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    {d q : Set E} (hd : IsFinitePLBallPair P2 d q)
    {f : E → X} (hf : PolyhedralPLInCharts e f d) (hfi : InjOn f d)
    (hfR : MapsTo f d R) (hproper : ∀ x ∈ d, f x ∈ frontier R ↔ x ∈ q)
    (hO : IsOpen O) (hfO : f '' d ⊆ O) :
    ∃ (H : Disk ≃ₜ d) (j : V2 → X) (P : OriginalDiskProduct e R j),
      H.IsFinitePL ∧ (∀ x : Disk, j x = f (H x)) ∧
      (∀ x : Disk, (x : V2) ∈ Rim ↔ (H x : E) ∈ q) ∧
      MapsTo P.map (Disk ×ˢ I) O ∧
      (∀ x : Disk, P.map ((x : V2), 0) = f (H x)) ∧
      P.map '' (Disk ×ˢ {(0 : ℝ)}) = f '' d ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (Disk ×ˢ Ioo (-ε) ε))) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' (P.map '' (Rim ×ˢ Ioo (-ε) ε))) := by
  have hDisk : IsFinitePLBallPair P2 Disk Rim :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨H, hH, hHrim⟩ := hDisk.exists_homeomorph hd
  have hHcopy := hH
  obtain ⟨u, hu, huval⟩ := hHcopy
  have humap : MapsTo u Disk d := by
    intro x hx
    rw [← huval ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hui : InjOn u Disk := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((huval ⟨x, hx⟩).trans (hxy.trans (huval ⟨y, hy⟩).symm))))
  have hju : PolyhedralPLInCharts e (f ∘ u) Disk := by
    obtain ⟨K, hK, hKs, hKf⟩ := hu
    rw [← hKs]
    exact hf.comp_finitePiecewiseAffineOn K hK ⟨K, hK, rfl, hKf⟩
      (fun _ hx ↦ humap (hKs.subset hx))
  have hji : InjOn (f ∘ u) Disk := hfi.comp hui humap
  let : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hje : Topology.IsEmbedding (fun x : Disk ↦ (f ∘ u) x) :=
    (hju.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy ↦ Subtype.ext (hji x.property y.property hxy))).isEmbedding
  have hproper' (x : Disk) : (f ∘ u) x ∈ frontier R ↔ (x : V2) ∈ Rim := by
    rw [Function.comp_apply, hproper _ (humap x.property), ← huval x]
    exact (hHrim x).symm
  obtain ⟨P, hPO, hopen⟩ := exists_small_original_disk_product hR he hju hje
    (fun x hx ↦ hfR (humap hx)) hproper' hO
    (image_subset_iff.mpr (fun x hx ↦ hfO ⟨u x, humap hx, rfl⟩))
  have hjval (x : Disk) : (f ∘ u) x = f (H x) := congrArg f (huval x).symm
  have hPval (x : Disk) : P.map ((x : V2), 0) = f (H x) :=
    (P.central x x.property).trans (hjval x)
  refine ⟨H, f ∘ u, P, hH, hjval, hHrim, hPO, hPval, ?_, hopen⟩
  apply Subset.antisymm
  · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have ht0 : t = 0 := ht
    subst t
    rw [hPval ⟨x, hx⟩]
    exact ⟨H ⟨x, hx⟩, (H ⟨x, hx⟩).property, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := H.surjective ⟨x, hx⟩
    exact ⟨((y : V2), 0), ⟨y.property, rfl⟩,
      (hPval y).trans (congrArg (fun z : d ↦ f z) hy)⟩

end PoincareConjecture.M76.Dehn.Annuli
