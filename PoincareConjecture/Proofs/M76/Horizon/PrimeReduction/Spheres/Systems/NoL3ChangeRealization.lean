import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RealizationTransport

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasPuncturedSphereModel.change_original_realization
    {X E F ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R : Set X}
    (hm : HasPuncturedSphereModel e f R)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x)
    (phi : X → F) (hphi : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphii : InjOn phi R) : HasPuncturedSphereModel e phi R := by
  obtain ⟨_,n,A,r,M,G,C,hA,hAdis,hG,hC,hmark⟩ := hm
  have hgG (x : R) : g (G x) = (x : X) := by
    rw [hG]
    exact (hreal x x.property).2
  have hgM (y : M) : g y = (G.symm y : X) := by
    simpa only [G.apply_symm_apply] using hgG (G.symm y)
  have hML : M ⊆ L.space := by
    intro y hy
    have h := (hreal (G.symm ⟨y,hy⟩) (G.symm ⟨y,hy⟩).property).1
    rwa [←hG,G.apply_symm_apply] at h
  have hgMR : MapsTo g M R := by
    intro y hy
    rw [hgM ⟨y,hy⟩]
    exact (G.symm ⟨y,hy⟩).property
  have hCcopy := hC
  obtain ⟨_,⟨J,hJ,hJM,_⟩,_⟩ := hCcopy
  have hcomp : FinitePiecewiseAffineOn (phi ∘ g) M := by
    rw [←hJM]
    exact (hg.restrict_finite J hJ (hJM.subset.trans hML)).finitePiecewiseAffineOn_comp J hJ hphi
  have hcompi : InjOn (phi ∘ g) M := by
    intro x hx y hy hxy
    have hxy' := hphii (hgMR hx) (hgMR hy) hxy
    have hh : G.symm ⟨x,hx⟩ = G.symm ⟨y,hy⟩ :=
      Subtype.ext ((hgM ⟨x,hx⟩).symm.trans (hxy'.trans (hgM ⟨y,hy⟩)))
    exact congrArg Subtype.val (G.symm.injective hh)
  obtain ⟨T,hT,hTval⟩ := hcomp.exists_homeomorph_image hcompi
  refine ⟨hphi,n,A,r,_,G.trans T,T.symm.trans C,hA,hAdis,?_,hT.symm.trans hC,?_⟩
  · intro x
    change (T (G x) : F) = phi x
    rw [hTval]
    exact congrArg phi (hgG x)
  · intro x
    change (x : X) ∈ frontier R ↔ (C (T.symm (T (G x))) : Fin 4 → ℝ) ∈ ⋃ i, r i
    rw [T.symm_apply_apply]
    exact hmark x

theorem HasNoPuncturedSphereComponents.change_original_realization
    {X E F ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R Q : Set X}
    (hno : HasNoPuncturedSphereComponents e f Q)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f R) (hQR : Q ⊆ R)
    (L : SimplicialComplex ℝ F) (g : F → X)
    (hg : PolyhedralPLInCharts e g L.space)
    (phi : X → F) (hreal : ∀ x ∈ R, phi x ∈ L.space ∧ g (phi x) = x) :
    HasNoPuncturedSphereComponents e phi Q := by
  intro x hx hm
  apply hno x hx
  exact hm.change_original_realization L g hg
    (fun y hy => hreal y (hQR (connectedComponentIn_subset _ _ hy))) f hf
    (hfi.mono ((connectedComponentIn_subset _ _).trans hQR))

end PoincareConjecture.M76
