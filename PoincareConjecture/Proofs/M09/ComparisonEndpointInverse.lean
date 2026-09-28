import PoincareConjecture.Proofs.M09.ManifoldLocalInverse
import PoincareConjecture.Proofs.M09.TriangularBijective
import PoincareConjecture.Proofs.M09.SmoothSquareAction

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def squareFamilyParameterDomain (Ω : Set (E × ℝ)) (τmax : ℝ) : Set (E × ℝ) :=
  {z | z.2 ∈ Set.Ioo 0 τmax ∧
    ∀ r ∈ Set.Icc (0 : ℝ) 1, (z.1, Real.sqrt z.2 * r) ∈ Ω}

theorem isOpen_squareFamilyParameterDomain (Ω : Set (E × ℝ)) (hΩ : IsOpen Ω)
    (τmax : ℝ) : IsOpen (squareFamilyParameterDomain Ω τmax) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hnear : ∀ᶠ w : E × ℝ in 𝓝 z,
      ∀ r ∈ Set.Icc (0 : ℝ) 1, (w.1, Real.sqrt w.2 * r) ∈ Ω := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    have hc : Continuous (fun w : (E × ℝ) × ℝ ↦
        (w.1.1, Real.sqrt w.1.2 * w.2)) :=
      continuous_fst.fst.prodMk ((Real.continuous_sqrt.comp continuous_fst.snd).mul continuous_snd)
    exact hc.continuousAt.preimage_mem_nhds (hΩ.mem_nhds (hz.2 r hr))
  filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
    (show z ∈ Set.univ ×ˢ Set.Ioo 0 τmax from ⟨Set.mem_univ _, hz.1⟩), hnear] with w hw hseg
  exact ⟨hw.2, hseg⟩

theorem squareFamilyParameterDomain_endpoint (Ω : Set (E × ℝ)) (τmax : ℝ)
    (z : E × ℝ) (hz : z ∈ squareFamilyParameterDomain Ω τmax) :
    (z.1, Real.sqrt z.2) ∈ Ω := by
  simpa only [mul_one] using hz.2 1 ⟨zero_le_one, le_rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem squareFamilyEndpoint_contMDiffOn (f : E × ℝ → M) (Ω : Set (E × ℝ))
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f Ω) (τmax : ℝ) :
    ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ (fun z ↦ f (z.1, Real.sqrt z.2))
      (squareFamilyParameterDomain Ω τmax) := by
  have hi : ContDiffOn ℝ ∞ (fun z : E × ℝ ↦ (z.1, Real.sqrt z.2))
      (squareFamilyParameterDomain Ω τmax) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.sqrt (fun _ hz ↦ hz.1.1.ne'))
  exact hf.comp hi.contMDiffOn (fun z hz ↦ squareFamilyParameterDomain_endpoint Ω τmax z hz)

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_squareFamily_endpoint_inverse
    (f : E × ℝ → M) (Ω : Set (E × ℝ)) (hΩ : IsOpen Ω)
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f Ω)
    (τmax : ℝ) (z : E × ℝ) (hz : z ∈ squareFamilyParameterDomain Ω τmax)
    (hbij : Function.Bijective (mfderiv (𝓘(ℝ, E)) (𝓡 n)
      (fun x ↦ f (x, Real.sqrt z.2)) z.1)) :
    ∃ e : OpenPartialHomeomorph (E × ℝ) (M × ℝ),
      z ∈ e.source ∧ e.source ⊆ squareFamilyParameterDomain Ω τmax ∧
        Set.EqOn e (fun w ↦ (f (w.1, Real.sqrt w.2), w.2)) e.source ∧
        ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, E × ℝ)) ∞ e.symm e.target := by
  let S := squareFamilyParameterDomain Ω τmax
  have hS := isOpen_squareFamilyParameterDomain Ω hΩ τmax
  let H : E × ℝ → M := fun w ↦ f (w.1, Real.sqrt w.2)
  have hH : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ H S :=
    squareFamilyEndpoint_contMDiffOn f Ω hf τmax
  have hHprod : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ H S := by
    convert! hH using 1 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hd := (hHprod.contMDiffAt (hS.mem_nhds hz)).mdifferentiableAt (by simp)
  let L := mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) ((𝓡 n).prod (𝓘(ℝ, ℝ)))
    (fun w : E × ℝ ↦ (H w, w.2)) z
  have hLb : Function.Bijective L := by
    dsimp only [L]
    rw [mfderiv_prodMk hd mdifferentiableAt_snd, mfderiv_snd]
    apply (triangular_bijective_iff (E := E) (F := EuclideanSpace ℝ (Fin n)) _
      (mfderiv (𝓘(ℝ, E)) (𝓡 n) (fun x ↦ f (x, Real.sqrt z.2)) z.1) ?_ ?_).mpr hbij
    · intro w
      rfl
    · intro w
      change mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (𝓡 n) H z (w, 0) = _
      rw [mfderiv_prod_eq_add_apply hd]
      simp only [map_zero, add_zero, H]
      rfl
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n) × ℝ) (M × ℝ) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin n)) M ℝ ℝ
  letI : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) ∞ (M × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) M ℝ
  let Φ : E × ℝ → M × ℝ := fun w ↦ (H w, w.2)
  have hΦ : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) ∞ Φ S := by
    convert! hHprod.prodMk contMDiffOn_snd using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hfull : Function.Bijective (mfderiv (𝓘(ℝ, E × ℝ))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) Φ z) := by
    convert! hLb using 1 <;> simp only [L, Φ, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    congr 2 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  obtain ⟨e, hze, hsub, he, hinv, _⟩ := exists_manifold_local_inverse Φ S hS hΦ z hz hfull
  refine ⟨e, hze, hsub, he, ?_⟩
  convert! hinv using 1 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]

end PoincareConjecture.Proofs.M09
