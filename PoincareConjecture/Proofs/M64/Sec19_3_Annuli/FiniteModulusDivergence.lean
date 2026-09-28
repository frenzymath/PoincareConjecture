import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteCurrentSlices
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteParameterEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusIntrinsicTension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64ParameterAnnulus_modulusEnergyDensity_eq_current_divergence
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    {Phi : ℝ × E → M} {O : Set (ℝ × E)} (hO : IsOpen O)
    (hPhi : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 n) ∞ Phi O)
    {h : LoopPlane → E} (hh : ContDiffOn ℝ 1 h m64AnnulusDomain)
    (hbase : ∀ p, Phi (0, h p) = A.map p)
    {x s : ℝ} (hp : (0, h (annulusPoint x s)) ∈ O)
    (hinside : annulusPoint x s ∈ m64AnnulusInterior) :
    let v := fun t p => Phi (t, h p)
    deriv (fun t => m64ModulusEnergyDensity g r (v t) (annulusPoint x s)) 0 =
      r * fderiv ℝ (m64FiniteAnnulusCurrent g v 0) (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1) +
      r⁻¹ * fderiv ℝ (m64FiniteAnnulusCurrent g v 1) (annulusPoint x s)
        (EuclideanSpace.single (1 : Fin 2) 1) := by
  let p := annulusPoint x s
  let v := fun t q => Phi (t, h q)
  change deriv (fun t => m64ModulusEnergyDensity g r (v t) p) 0 =
    r * fderiv ℝ (m64FiniteAnnulusCurrent g v 0) p (EuclideanSpace.single (0 : Fin 2) 1) +
      r⁻¹ * fderiv ℝ (m64FiniteAnnulusCurrent g v 1) p (EuclideanSpace.single (1 : Fin 2) 1)
  have hsub : m64AnnulusInterior ⊆ interior m64AnnulusDomain :=
    interior_maximal m64AnnulusInterior_subset_domain isOpen_m64AnnulusInterior
  have hneigh : m64AnnulusDomain ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp (hsub hinside)
  have hhAt : ContDiffAt ℝ 1 h p := hh.contDiffAt hneigh
  have hh0 : DifferentiableAt ℝ (fun y => h (annulusPoint y s)) x :=
    (hhAt.differentiableAt one_ne_zero).comp x
      (m64AnnulusPoint_horizontal_hasDerivAt s x).differentiableAt
  have hh1 : DifferentiableAt ℝ (fun y => h (annulusPoint x y)) s :=
    (hhAt.differentiableAt one_ne_zero).comp s
      (m64AnnulusPoint_vertical_hasDerivAt x s).differentiableAt
  have hAv : ContMDiffOn (𝓡 2) (𝓡 n) ∞ (v 0) m64AnnulusInterior := by
    change ContMDiffOn (𝓡 2) (𝓡 n) ∞ (fun q => Phi (0, h q)) m64AnnulusInterior
    rw [funext hbase]
    exact hA
  have hX0 := ((m64Annulus_horizontal_velocity_contMDiffAt
    isOpen_m64AnnulusInterior hAv hinside).comp x
      (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt).mdifferentiableAt (by simp)
  have hX1 := ((m64Annulus_vertical_velocity_contMDiffAt
    isOpen_m64AnnulusInterior hAv hinside).comp s
      (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt).mdifferentiableAt (by simp)
  have h0 := m64ParameterMotion_half_energy_hasDerivAt D hO hPhi hh0 hp
  have h1 := m64ParameterMotion_half_energy_hasDerivAt D hO hPhi hh1 hp
  have hdiv0 := m64ParameterMotion_energy_derivative_eq_divergence D hO hPhi hh0 hp hX0
  have hdiv1 := m64ParameterMotion_energy_derivative_eq_divergence D hO hPhi hh1 hp hX1
  have hdensity : HasDerivAt
      (fun t => m64ModulusEnergyDensity g r (v t) p)
      (r * g.inner (v 0 p)
        (rampHorizontalCovariantDerivative D (fun y => v 0 (annulusPoint y s))
          (fun y => curveVelocity (fun t => v t (annulusPoint y s)) 0) x)
        (curveVelocity (fun y => v 0 (annulusPoint y s)) x) +
      r⁻¹ * g.inner (v 0 p)
        (rampHorizontalCovariantDerivative D (fun y => v 0 (annulusPoint x y))
          (fun y => curveVelocity (fun t => v t (annulusPoint x y)) 0) s)
        (curveVelocity (fun y => v 0 (annulusPoint x y)) s)) 0 := by
    apply ((h0.const_mul r).add (h1.const_mul r⁻¹)).congr_of_eventuallyEq
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt
      (hO.mem_nhds hp)] with t ht
    have hmd : MDifferentiableAt (𝓡 2) (𝓡 n) (v t) p :=
      ((hPhi.contMDiffAt (hO.mem_nhds ht)).mdifferentiableAt (by simp)).comp p
        ((differentiableAt_const t).prodMk
          (hhAt.differentiableAt one_ne_zero)).mdifferentiableAt
    dsimp only [Pi.add_apply]
    rw [m64Annulus_horizontal_velocity hmd, m64Annulus_vertical_velocity hmd]
    simp only [m64ModulusEnergyDensity, m60AreaGram, EuclideanSpace.basisFun_apply]
    ring
  have hV : ContMDiffAt (𝓡 2) ((𝓡 n).prod (𝓡 n)) 1 (fun q =>
      (⟨v 0 q, curveVelocity (fun t => v t q) 0⟩ : TangentBundle (𝓡 n) M)) p :=
    ((m64ParameterMotion_timeVelocity_contMDiffAt hO hPhi hp).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by simp)).comp p
        ((contDiffAt_const.prodMk hhAt).contMDiffAt)
  have hJ (i : Fin 2) : DifferentiableAt ℝ (m64FiniteAnnulusCurrent g v i) p :=
    m64FiniteAnnulusCurrent_differentiableAt g (hsub hinside)
      (hAv.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hinside)) hV i
  have hnear0 : ∀ᶠ y in 𝓝 x, annulusPoint y s ∈ m64AnnulusInterior :=
    (m64AnnulusPoint_horizontal_hasDerivAt s x).continuousAt
      (isOpen_m64AnnulusInterior.mem_nhds hinside)
  have hnear1 : ∀ᶠ y in 𝓝 s, annulusPoint x y ∈ m64AnnulusInterior :=
    (m64AnnulusPoint_vertical_hasDerivAt x s).continuousAt
      (isOpen_m64AnnulusInterior.mem_nhds hinside)
  have hcur0 := m64FiniteAnnulusCurrent_along_slice_hasDerivAt g (v := v) 0 (hJ 0)
    (fun y => by simpa only [EuclideanSpace.basisFun_apply] using
      m64AnnulusPoint_horizontal_hasDerivAt s y)
    (hnear0.mono fun _ hy => hsub hy)
    (hnear0.mono fun _ hy =>
      (hAv.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hy)).mdifferentiableAt (by simp))
  have hcur1 := m64FiniteAnnulusCurrent_along_slice_hasDerivAt g (v := v) 1 (hJ 1)
    (fun y => by simpa only [EuclideanSpace.basisFun_apply] using
      m64AnnulusPoint_vertical_hasDerivAt x y)
    (hnear1.mono fun _ hy => hsub hy)
    (hnear1.mono fun _ hy =>
      (hAv.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hy)).mdifferentiableAt (by simp))
  have htension : r • rampHorizontalCovariantDerivative D
        (fun y => v 0 (annulusPoint y s))
        (fun y => curveVelocity (fun z => v 0 (annulusPoint z s)) y) x +
      r⁻¹ • rampHorizontalCovariantDerivative D (fun y => v 0 (annulusPoint x y))
        (fun y => curveVelocity (fun z => v 0 (annulusPoint x z)) y) s = 0 := by
    have htransport := congrArg (fun f : LoopPlane → M =>
      (r • rampHorizontalCovariantDerivative D (fun y => f (annulusPoint y s))
          (fun y => curveVelocity (fun z => f (annulusPoint z s)) y) x +
        r⁻¹ • rampHorizontalCovariantDerivative D (fun y => f (annulusPoint x y))
          (fun y => curveVelocity (fun z => f (annulusPoint x z)) y) s :
            EuclideanSpace ℝ (Fin n))) (funext hbase)
    exact htransport.trans (m64Annulus_intrinsic_tension_eq_zero_of_modulus_minimum
      D A hr hminimum hconformal hA hinside)
  have hpair := congrArg (fun w : TangentSpace (𝓡 n) (v 0 p) =>
    g.inner (v 0 p) (curveVelocity (fun t => v t p) 0) w) htension
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at hpair
  rw [h0.deriv] at hdiv0
  rw [h1.deriv] at hdiv1
  rw [hcur0.deriv] at hdiv0
  rw [hcur1.deriv] at hdiv1
  rw [hdensity.deriv]
  simp only [EuclideanSpace.basisFun_apply] at *
  dsimp only [v, p] at *
  linear_combination r * hdiv0 + r⁻¹ * hdiv1 - hpair

end PoincareConjecture
