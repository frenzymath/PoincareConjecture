import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight

set_option autoImplicit false

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]

theorem exists_collar_surface_source_pullback
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (c : M → E3) {U : Set M} (hU : IsOpen U)
    (hc : ContMDiffOn I 𝓘(ℝ, E3) ∞ c U) (hci : InjOn c U)
    (hcd : ∀ p ∈ U, Injective (mfderiv I 𝓘(ℝ, E3) c p))
    (hcentral : MapsTo c U (range (fun p : UnitTwoSphere => ψ (p, 0)))) :
    ∃ q : M → UnitTwoSphere,
      ContMDiffOn I (𝓡 2) ∞ q U ∧ InjOn q U ∧
      (∀ p ∈ U, Injective (mfderiv I (𝓡 2) q p)) ∧
      ∀ p ∈ U, ψ (q p, 0) = c p := by
  obtain ⟨ec, hec, hsource, htarget, heci⟩ := exists_collar_chart ψ hψ
  let q : M → UnitTwoSphere := fun p => (ec.symm (c p)).1
  have hsource0 (p : UnitTwoSphere) : (p, (0 : ℝ)) ∈ ec.source := by
    rw [hsource]
    exact ⟨mem_univ _, by norm_num⟩
  have hcU (p : M) (hp : p ∈ U) : c p ∈ ec.target := by
    rw [htarget]
    obtain ⟨a, ha⟩ := hcentral hp
    exact ⟨(a, 0), ⟨mem_univ _, by norm_num⟩, ha⟩
  have hq : ContMDiffOn I (𝓡 2) ∞ q U :=
    (contMDiff_fst.comp_contMDiffOn heci).comp hc hcU
  have hrec : EqOn ((fun a : UnitTwoSphere => ψ (a, 0)) ∘ q) c U := by
    intro p hp
    obtain ⟨a, ha⟩ := hcentral hp
    have hinv : ec.symm (c p) = (a, 0) := by
      calc
        ec.symm (c p) = ec.symm (ec (a, 0)) :=
          congrArg ec.symm ((congrFun hec (a, 0)).trans ha).symm
        _ = (a, 0) := ec.left_inv (hsource0 a)
    change ψ ((ec.symm (c p)).1, 0) = c p
    rw [hinv]
    exact ha
  refine ⟨q, hq, ?_, ?_, hrec⟩
  · intro p hp r hr hpr
    apply hci hp hr
    rw [← hrec hp, ← hrec hr]
    exact congrArg (fun a : UnitTwoSphere => ψ (a, 0)) hpr
  · intro p hp
    have hd := ((collar_central_contMDiff ψ hψ).mdifferentiable
      (by simp) (q p)).hasMFDerivAt.comp p
        ((hq.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)).hasMFDerivAt
    have hagree : (fun a : UnitTwoSphere => ψ (a, 0)) ∘ q =ᶠ[𝓝 p] c :=
      Filter.mem_of_superset (hU.mem_nhds hp) hrec
    have hderiv := hd.mfderiv
    rw [hagree.mfderiv_eq] at hderiv
    intro a b hab
    apply hcd p hp
    rw [hderiv]
    exact congrArg
      (mfderiv (𝓡 2) 𝓘(ℝ, E3) (fun r : UnitTwoSphere => ψ (r, 0)) (q p)) hab

end PoincareConjecture.M25.Topology3D
