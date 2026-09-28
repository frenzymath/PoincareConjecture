import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel
import Mathlib.Topology.Homeomorph.Lemmas
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFiniteModelBallImages
import PoincareConjecture.Proofs.M76.Mathlib.CompatibleChartPLMaps










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem HasPuncturedSphereModel.image_original_realization
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R : Set X}
    (hm : HasPuncturedSphereModel e f R) (F : X ≃ₜ X)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R ∪ F '' R, f x ∈ L.space ∧ g (f x) = x)
    (hfF : ∀ i, LocallyPiecewiseAffineOn ((f ∘ F) ∘ (e i).symm) (e i).target) :
    HasPuncturedSphereModel e f (F '' R) := by
  obtain ⟨hf, n, A, r, M, G, C, hA, hAdis, hG, hC, hmark⟩ := hm
  have hgG (x : R) : g (G x) = (x : X) := by
    rw [hG]
    exact (hreal x (Or.inl x.property)).2
  have hgM (y : M) : g y = (G.symm y : X) := by
    simpa only [G.apply_symm_apply] using hgG (G.symm y)
  have hML : M ⊆ L.space := by
    intro y hy
    have h := (hreal (G.symm ⟨y, hy⟩) (Or.inl (G.symm ⟨y, hy⟩).property)).1
    rw [← hG, G.apply_symm_apply] at h
    exact h
  have hgMR : MapsTo g M R := by
    intro y hy
    rw [hgM ⟨y, hy⟩]
    exact (G.symm ⟨y, hy⟩).property
  have hfi : InjOn f (F '' R) := by
    intro x hx y hy hxy
    exact ((hreal x (Or.inr hx)).2).symm.trans
      ((congrArg g hxy).trans (hreal y (Or.inr hy)).2)
  have hCcopy := hC
  obtain ⟨_, ⟨J, hJ, hJM, _⟩, _⟩ := hCcopy
  have hcomp : FinitePiecewiseAffineOn ((f ∘ F) ∘ g) M := by
    rw [← hJM]
    exact (hg.restrict_finite J hJ (hJM.subset.trans hML)).finitePiecewiseAffineOn_comp J hJ hfF
  have hcompi : InjOn ((f ∘ F) ∘ g) M := by
    intro x hx y hy hxy
    apply hgi (hML hx) (hML hy)
    apply F.injective
    exact hfi (mem_image_of_mem F (hgMR hx)) (mem_image_of_mem F (hgMR hy)) hxy
  obtain ⟨T, hT, hTval⟩ := hcomp.exists_homeomorph_image hcompi
  let G' := (F.image R).symm.trans (G.trans T)
  let C' := T.symm.trans C
  have hG' (x : F '' R) : (G' x : E) = f x := by
    change (T (G ((F.image R).symm x)) : E) = f x
    rw [hTval]
    change f (F (g (G ((F.image R).symm x)))) = f x
    rw [hgG]
    exact congrArg f (congrArg Subtype.val ((F.image R).apply_symm_apply x))
  refine ⟨hf, n, A, r, _, G', C', hA, hAdis, hG', hT.symm.trans hC, ?_⟩
  intro x
  change (x : X) ∈ frontier (F '' R) ↔
    (C (T.symm (T (G ((F.image R).symm x)))) : Fin 4 → ℝ) ∈ ⋃ i, r i
  rw [T.symm_apply_apply, ← hmark]
  change (x : X) ∈ frontier (F '' R) ↔ F.symm x ∈ frontier R
  rw [← F.image_frontier R]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have heq : y = F.symm x := F.injective (hyx.trans (F.apply_symm_apply x).symm)
    exact heq ▸ hy
  · intro hx
    exact ⟨F.symm x, hx, F.apply_symm_apply x⟩

theorem HasNoPuncturedSphereComponents.image_original_realization
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {Q : Set X}
    (hno : HasNoPuncturedSphereComponents e f Q) (F : X ≃ₜ X)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ Q ∪ F '' Q, f x ∈ L.space ∧ g (f x) = x)
    (hfF : ∀ i, LocallyPiecewiseAffineOn ((f ∘ F.symm) ∘ (e i).symm) (e i).target) :
    HasNoPuncturedSphereComponents e f (F '' Q) := by
  rintro _ ⟨x, hx, rfl⟩ hm
  have hcomp : F.symm '' connectedComponentIn (F '' Q) (F x) = connectedComponentIn Q x := by
    rw [← F.image_connectedComponentIn hx]
    exact F.toEquiv.symm_image_image _
  apply hno x hx
  rw [← hcomp]
  apply hm.image_original_realization F.symm L g hg hgi _ hfF
  intro y hy
  apply hreal
  rcases hy with hy | hy
  · exact Or.inr (connectedComponentIn_subset _ _ hy)
  · exact Or.inl (connectedComponentIn_subset _ _ (hcomp.subset hy))

theorem locallyPiecewiseAffineOn_comp_inverse_original_move
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ι → OpenPartialHomeomorph X V3) (f : X → E)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (F : X ≃ₜ X)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) (i : ι) :
    LocallyPiecewiseAffineOn ((f ∘ F.symm) ∘ (e i).symm) (e i).target := by
  have h := OpenPartialHomeomorph.locallyPiecewiseAffineOn_compatible_chart e hcover hf
    (F.toOpenPartialHomeomorph.trans (e i)) (fun j => hF j i)
  have ht : (F.toOpenPartialHomeomorph.trans (e i)).target = (e i).target := by
    simp only [OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
      preimage_univ, inter_univ]
  rw [ht] at h
  exact h

theorem HasNoPuncturedSphereComponents.image_of_original_atlas_move
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {Q : Set X}
    (hno : HasNoPuncturedSphereComponents e f Q) (F : X ≃ₜ X)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ Q ∪ F '' Q, f x ∈ L.space ∧ g (f x) = x) :
    HasNoPuncturedSphereComponents e f (F '' Q) :=
  hno.image_original_realization F L g hg hgi hreal
    (locallyPiecewiseAffineOn_comp_inverse_original_move e f hcover hf F hF)

theorem HasNoPuncturedSphereComponents.image_of_supported_original_move
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {Q D T : Set X}
    (hno : HasNoPuncturedSphereComponents e f Q) (F : X ≃ₜ X)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hQD : Q ⊆ D) (hTD : T ⊆ D) (hfix : EqOn F id Tᶜ)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ D, f x ∈ L.space ∧ g (f x) = x) :
    HasNoPuncturedSphereComponents e f (F '' Q) := by
  have hmap : MapsTo F D D := by
    intro x hx
    by_contra hn
    have hFx : F (F x) = F x := hfix (fun h => hn (hTD h))
    exact hn ((F.injective hFx).symm ▸ hx)
  apply hno.image_of_original_atlas_move F hcover hf hF L g hg hgi
  intro x hx
  apply hreal
  rcases hx with hx | ⟨y, hy, rfl⟩
  · exact hQD hx
  · exact hmap (hQD hy)

end PoincareConjecture.M76
