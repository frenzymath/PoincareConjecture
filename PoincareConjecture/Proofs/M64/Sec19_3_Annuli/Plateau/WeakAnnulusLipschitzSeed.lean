import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedLipschitz
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LipschitzVectorGreen












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S




theorem m64ObservedWeakAnnulus_of_annulus [CompactSpace M]
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) :
    ∃ W : M64ObservedWeakAnnulus (n := n) e c0 c1, W.map = A.map ∧
      ∀ i, ∀ᵐ p ∂mu, W.column i p =
        fderiv ℝ (e ∘ A.map) p (EuclideanSpace.single i 1) := by
  let f : LoopPlane → E := e ∘ A.map
  obtain ⟨K, hLip⟩ := m64Annulus_observed_lipschitzOn A e he
  have hA : ∀ᵐ p ∂mu, MDifferentiableAt (𝓡 2) (𝓡 n) A.map p := by
    filter_upwards [ae_restrict_of_ae A.ae_manifold_differentiable,
      ae_restrict_mem isOpen_interior.measurableSet] with p hp hm
    exact hp (interior_subset hm)
  have hdiff : ∀ᵐ p ∂mu, DifferentiableAt ℝ f p := by
    filter_upwards [hA] with p hp
    exact mdifferentiableAt_iff_differentiableAt.mp
      ((he.mdifferentiable (by simp) _).comp p hp)
  let D : Fin 2 → LoopPlane → E := fun i p =>
    fderiv ℝ f p (EuclideanSpace.single i 1)
  have hcolumn (i : Fin 2) : MemLp (D i) 2 mu :=
    m64_lipschitz_vector_column_memLp hLip hdiff i
  let column : Fin 2 → Lp E 2 mu := fun i => (hcolumn i).toLp (D i)
  have hcoe (i : Fin 2) : column i =ᵐ[mu] D i := (hcolumn i).coeFn_toLp
  have htangent (i : Fin 2) :
      ∀ᵐ p ∂mu, D i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (A.map p)) := by
    filter_upwards [hA] with p hp
    refine ⟨mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single i 1), ?_⟩
    have hc := mfderiv_comp p (he.mdifferentiable (by simp) _) hp
    have hd := congrArg (fun L => L (EuclideanSpace.single i 1)) hc
    rw [mfderiv_eq_fderiv] at hd
    exact hd.symm
  let W : M64ObservedWeakAnnulus (n := n) e c0 c1 := {
    map := A.map
    observed_memLp := m64_lipschitz_memLp_two hLip
    column := column
    tangent := fun i => by
      filter_upwards [hcoe i, htangent i] with p hp ht
      exact hp ▸ ht
    weak_partial := fun i b => m64WeakPartialDeriv_ae_congr EventuallyEq.rfl
      ((hcoe i).symm.mono fun p hp => congrArg (fun v : E => v b) hp)
      (m64_lipschitz_vector_weak_partial hLip hdiff i b)
    boundary := by
      intro phi hphi
      have hh := m64Annulus_vertical_green_lipschitzOn_vector hLip hdiff hphi
      have heq : (∫ p in S, phi p • column 1 p) = ∫ p in S, phi p • D 1 p :=
        integral_congr_ae ((hcoe 1).mono fun p hp => congrArg (fun v : E => phi p • v) hp)
      rw [heq]
      simpa only [D, f, Function.comp_apply, A.upper_boundary, A.lower_boundary] using hh
    seam := by
      intro phi hphi hseam
      have heq : (∫ p in S, phi p • column 0 p) = ∫ p in S, phi p • D 0 p :=
        integral_congr_ae ((hcoe 0).mono fun p hp => congrArg (fun v : E => phi p • v) hp)
      rw [heq]
      apply m64Annulus_periodic_green_lipschitzOn_vector hLip hdiff hphi _ hseam
      intro s _
      simpa only [Function.comp_apply, zero_add] using congrArg e (A.periodic 0 s) }
  exact ⟨W, rfl, hcoe⟩

end PoincareConjecture
