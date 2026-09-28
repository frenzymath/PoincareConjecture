import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeRampCirclePositivity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSmoothGram
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusCirclePositivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

omit [T2Space M] [CompactSpace M] in
private theorem weighted_conformal_on_interior_of_ae
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) {r : ℝ}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 =
          r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    ∀ p ∈ m64AnnulusInterior,
      r * m60AreaGram g A.map p 0 0 =
          r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0 := by
  have hcont (i j : Fin 2) :
      ContinuousOn (fun p => m60AreaGram g A.map p i j) m64AnnulusInterior := by
    intro p hp
    exact (m64AreaGram_entry_contDiffAt
      (hf.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hp)) i j).continuousAt.continuousWithinAt
  rw [Measure.restrict_congr_set m64AnnulusDomain_ae_eq_interior] at hconformal
  have hclosure : m64AnnulusInterior ⊆ closure (interior m64AnnulusInterior) := by
    rw [isOpen_m64AnnulusInterior.interior_eq]
    exact subset_closure
  have hleft : ContinuousOn
      (fun p => r * m60AreaGram g A.map p 0 0) m64AnnulusInterior :=
    continuousOn_const.mul (hcont 0 0)
  have hright : ContinuousOn
      (fun p => r⁻¹ * m60AreaGram g A.map p 1 1) m64AnnulusInterior :=
    continuousOn_const.mul (hcont 1 1)
  have hdiag := MeasureTheory.Measure.eqOn_of_ae_eq
    (hconformal.mono fun _ h => h.1) hleft hright hclosure
  have hcross := MeasureTheory.Measure.eqOn_of_ae_eq
    (hconformal.mono fun _ h => h.2) (hcont 0 1) continuousOn_const hclosure
  exact fun p hp => ⟨hdiag hp, hcross hp⟩

private theorem injective_of_positive_columns {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : E →L[ℝ] E →L[ℝ] ℝ) (d : LoopPlane →L[ℝ] E)
    (h00 : 0 < G (d (EuclideanSpace.single (0 : Fin 2) 1))
      (d (EuclideanSpace.single (0 : Fin 2) 1)))
    (h11 : 0 < G (d (EuclideanSpace.single (1 : Fin 2) 1))
      (d (EuclideanSpace.single (1 : Fin 2) 1)))
    (h01 : G (d (EuclideanSpace.single (0 : Fin 2) 1))
      (d (EuclideanSpace.single (1 : Fin 2) 1)) = 0)
    (h10 : G (d (EuclideanSpace.single (1 : Fin 2) 1))
      (d (EuclideanSpace.single (0 : Fin 2) 1)) = 0) : Function.Injective d := by
  let e0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let e1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  change G (d e0) (d e1) = 0 at h01
  change G (d e1) (d e0) = 0 at h10
  have hdecomp (v : LoopPlane) : v = v 0 • e0 + v 1 • e1 := by
    ext i
    fin_cases i <;> simp [e0, e1]
  have hd (v : LoopPlane) : d v = v 0 • d e0 + v 1 • d e1 := by
    rw [← map_smul, ← map_smul, ← map_add, ← hdecomp]
  have hker (v : LoopPlane) (hv : d v = 0) : v = 0 := by
    have h0 := congrArg (fun w => G w (d e0)) hv
    have h1 := congrArg (fun w => G w (d e1)) hv
    rw [hd v] at h0 h1
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      h10, h01, mul_zero, zero_add, add_zero, map_zero, zero_apply] at h0 h1
    have hv0 : v 0 = 0 := (mul_eq_zero.mp h0).resolve_right h00.ne'
    have hv1 : v 1 = 0 := (mul_eq_zero.mp h1).resolve_right h11.ne'
    calc
      v = v 0 • e0 + v 1 • e1 := hdecomp v
      _ = 0 := by rw [hv0, hv1, zero_smul, zero_smul, add_zero]
  intro v w hvw
  exact sub_eq_zero.mp (hker (v - w) (by rw [map_sub, hvw, sub_self]))

theorem m64FreeRampModulusMinimum_mfderiv_injective
    (P : M62.CircleProductData F circumference) (hcirc : 0 < circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point}
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 c1)
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (hr0 : M63IsRampAt P c0 t) (hr1 : M63IsRampAt P c1 t)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (P.flow.metric t) (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t)
      (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hA : ∀ p ∈ m64AnnulusDomain,
      ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ A.map p) :
    ∀ p ∈ m64AnnulusInterior,
      Function.Injective (mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p) := by
  have hpos := m64FreeRampModulusMinimum_circleCurrent_pos P hcirc t hc0 hc1 hp0 hp1
    hr0 hr1 sigma0 sigma1 A hr hminimum hconformal hA
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  have hconf := weighted_conformal_on_interior_of_ae A
    (fun p hp => (hA p (hsub hp)).contMDiffWithinAt) hconformal
  intro p hp
  have hpstrip : p ∈ m64AnnulusOpenStrip := by
    change p 1 ∈ Ioo (0 : ℝ) 1
    simpa only [Pi.zero_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      using hp 1 (mem_univ _)
  have hcol := m64Annulus_horizontal_column_ne_zero_of_circleCurrent_pos P t (hpos p hpstrip)
  have h00 := (P.flow.metric t).pos (A.map p) _ hcol
  have hweighted := (hconf p hp).1
  have hcross := (hconf p hp).2
  have h10 : m60AreaGram (P.flow.metric t) A.map p 1 0 = 0 :=
    (m60AreaGram_symm (P.flow.metric t) A.map p 1 0).trans hcross
  simp only [m60AreaGram, EuclideanSpace.basisFun_apply] at hweighted hcross h10
  have hleft : 0 < r * m60AreaGram (P.flow.metric t) A.map p 0 0 := by
    simpa only [m60AreaGram, EuclideanSpace.basisFun_apply] using (mul_pos hr h00)
  have hright : 0 < r⁻¹ *
      ((P.flow.metric t).inner (A.map p)
        ((mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p)
          (EuclideanSpace.single (1 : Fin 2) 1))
        ((mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p)
          (EuclideanSpace.single (1 : Fin 2) 1))) := by
    rw [← hweighted]
    simpa only [m60AreaGram, EuclideanSpace.basisFun_apply] using hleft
  have h11 : 0 <
      (P.flow.metric t).inner (A.map p)
        ((mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p)
          (EuclideanSpace.single (1 : Fin 2) 1))
        ((mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p)
          (EuclideanSpace.single (1 : Fin 2) 1)) := by
    rcases (mul_pos_iff.mp hright) with h | h
    · exact h.2
    · exact (not_lt_of_ge (le_of_lt (inv_pos.mpr hr))) h.1 |>.elim
  exact injective_of_positive_columns (E := EuclideanSpace ℝ (Fin (n + 1)))
    ((P.flow.metric t).inner (A.map p))
    (mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p) h00 h11 hcross h10

end PoincareConjecture
