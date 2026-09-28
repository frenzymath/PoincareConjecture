import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeComponentSubregions
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RealizationTransport
import PoincareConjecture.Proofs.M76.PrimeReduction.SphereAmbientTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.PLDomainAmbientTransport

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasNoPuncturedSphereComponents.of_moved_relative_component_subregions
    {X E ι ν μ : Type*} [TopologicalSpace X] [T2Space X] [Finite ν] [Finite μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R Q Q' T Z : Set X}
    (hno : HasNoPuncturedSphereComponents e f Q)
    (hQ : IsCompact Q) (hPL : PLDomain e Q)
    (hQ' : IsCompact Q') (hPL' : PLDomain e Q')
    (hZ : IsClosed Z)
    (B : ν → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hZB : Disjoint Z (⋃ i, B i)) (hfront : frontier Q = Z ∪ ⋃ i, B i)
    (B' : μ → Set X) (sB' : ∀ i, ChartwisePLSphere e (B' i))
    (hZB' : Disjoint Z (⋃ i, B' i)) (hfront' : frontier Q' = Z ∪ ⋃ i, B' i)
    (F : X ≃ₜ X)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hfix : EqOn F id Tᶜ) (hTR : T ⊆ R) (hfixZ : EqOn F id Z)
    (hQR : Q ⊆ R) (hQ'R : Q' ⊆ R)
    (hsub : F '' Q ⊆ Q')
    (hmeet : ∀ x ∈ Q', ∃ y ∈ Q, F y ∈ connectedComponentIn Q' x)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x) :
    HasNoPuncturedSphereComponents e f Q' := by
  classical
  have hmoved := hno.image_of_supported_original_move F hPL.cover hf hF
    hQR hTR hfix L g hg hgi hreal
  have hZF : F '' Z = Z := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      simpa only [hfixZ hz,id_eq] using hz
    · intro z hz
      exact ⟨z,hz,hfixZ hz⟩
  let Bm : ν → Set X := fun i => F '' B i
  let sBm : ∀ i, ChartwisePLSphere e (Bm i) :=
    fun i => ((sB i).nonempty_image F hPL.cover hF).some
  have hBmdis : Pairwise fun i j => Disjoint (Bm i) (Bm j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,hyx⟩
    exact disjoint_left.mp (hBdis hij) hx (F.injective hyx ▸ hy)
  have hZBm : Disjoint Z (⋃ i, Bm i) := by
    apply disjoint_left.mpr
    intro z hz hzm
    obtain ⟨i,y,hy,hyz⟩ := mem_iUnion.mp hzm
    have heq : y = z := F.injective (hyz.trans (hfixZ hz).symm)
    exact disjoint_left.mp hZB hz (mem_iUnion.mpr ⟨i,heq ▸ hy⟩)
  have hfrontm : frontier (F '' Q) = Z ∪ ⋃ i, Bm i := by
    rw [←F.image_frontier,hfront,image_union,hZF,image_iUnion]
  intro x hx hm
  obtain ⟨y,hy,hyC⟩ := hmeet x hx
  exact hmoved (F y) (mem_image_of_mem F hy)
    (hm.of_original_relative_cut_component (hQ.image F.continuous)
      (hPL.image_of_original_atlas_move F hF) hQ' hPL' hsub hZ
      Bm sBm hBmdis hZBm hfrontm B' sB' hZB' hfront'
      L g hg hgi (fun z hz => hreal z (hQ'R hz)) hx (mem_image_of_mem F hy) hyC)

end PoincareConjecture.M76
