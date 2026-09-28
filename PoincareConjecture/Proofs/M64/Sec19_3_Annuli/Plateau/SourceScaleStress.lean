import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalHarmonicStress
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceRescaling

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64AreaGram_sourceScale (g : RiemannianMetric n M) (s : ℝ) (hs : s ≠ 0)
    {f : LoopPlane → M} {p : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (m64SourceScale s hs p)) (i j : Fin 2) :
    m60AreaGram g (f ∘ m64SourceScale s hs) p i j =
      m64SourceScaleFactor s i * m64SourceScaleFactor s j *
        m60AreaGram g f (m64SourceScale s hs p) i j := by
  let D := m64SourceScale s hs
  have hD : MDifferentiableAt (𝓡 2) (𝓡 2) D p :=
    mdifferentiableAt_iff_differentiableAt.mpr D.differentiableAt
  have hd := mfderiv_comp p hf hD
  rw [mfderiv_eq_fderiv, D.fderiv] at hd
  have hbase (i : Fin 2) : D (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      m64SourceScaleFactor s i • EuclideanSpace.basisFun (Fin 2) ℝ i := by
    simpa only [EuclideanSpace.basisFun_apply] using m64SourceScale_basis s hs i
  have hv (i : Fin 2) : mfderiv (𝓡 2) (𝓡 n) (f ∘ D) p
      (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      m64SourceScaleFactor s i • mfderiv (𝓡 2) (𝓡 n) f (D p)
        (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    rw [hd]
    change mfderiv (𝓡 2) (𝓡 n) f (D p)
      (D (EuclideanSpace.basisFun (Fin 2) ℝ i)) = _
    rw [hbase, map_smul]
  change g.inner (f (D p))
    (mfderiv (𝓡 2) (𝓡 n) (f ∘ D) p (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (mfderiv (𝓡 2) (𝓡 n) (f ∘ D) p (EuclideanSpace.basisFun (Fin 2) ℝ j)) = _
  rw [hv i, hv j]
  simp only [map_smul, smul_apply, smul_eq_mul]
  change _ = _ * _ * g.inner (f (D p)) _ _
  ring

theorem m64WeightedStress_of_rescaled (g : RiemannianMetric n M)
    {f : LoopPlane → M} {O : Set LoopPlane} (hO : IsOpen O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f O) {p : LoopPlane} (hp : p ∈ O)
    {r : ℝ} (hr : 0 < r)
    (hcr : let D := m64SourceScale (Real.sqrt r) (Real.sqrt_pos.mpr hr).ne'
      let G := m60AreaGram g (f ∘ D)
      let e := EuclideanSpace.basisFun (Fin 2) ℝ
      fderiv ℝ (fun z => G z 0 0 - G z 1 1) (D.symm p) (e 0) =
          fderiv ℝ (fun z => -2 * G z 0 1) (D.symm p) (e 1) ∧
        fderiv ℝ (fun z => G z 0 0 - G z 1 1) (D.symm p) (e 1) =
          -fderiv ℝ (fun z => -2 * G z 0 1) (D.symm p) (e 0)) :
    let G := m60AreaGram g f
    let U := fun z => r * G z 0 0 - r⁻¹ * G z 1 1
    let W := fun z => -2 * G z 0 1
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    fderiv ℝ U p (e 0) = r⁻¹ * fderiv ℝ W p (e 1) ∧
      fderiv ℝ U p (e 1) = -r * fderiv ℝ W p (e 0) := by
  let s := Real.sqrt r
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have hs2 : s ^ 2 = r := Real.sq_sqrt hr.le
  have hss : s * s = r := by nlinarith only [hs2]
  have his : s⁻¹ * s⁻¹ = r⁻¹ := by rw [← mul_inv_rev, hss]
  have hfac0 : m64SourceScaleFactor s 0 = s := rfl
  have hfac1 : m64SourceScaleFactor s 1 = s⁻¹ := rfl
  let D := m64SourceScale s hs
  let G := m60AreaGram g f
  let U := fun z => r * G z 0 0 - r⁻¹ * G z 1 1
  let W := fun z => -2 * G z 0 1
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hpair (i j : Fin 2) :
      (fun z => m60AreaGram g (f ∘ D) z i j) =ᶠ[𝓝 (D.symm p)]
        (fun z => m64SourceScaleFactor s i * m64SourceScaleFactor s j * G (D z) i j) := by
    have hn : D ⁻¹' O ∈ 𝓝 (D.symm p) :=
      D.continuous.continuousAt.preimage_mem_nhds
        (by simpa only [D.apply_symm_apply] using hO.mem_nhds hp)
    filter_upwards [hn] with z hz
    exact m64AreaGram_sourceScale g s hs
      ((hf.contMDiffAt (hO.mem_nhds hz)).mdifferentiableAt (by simp)) i j
  have hA : (fun z => m60AreaGram g (f ∘ D) z 0 0 -
      m60AreaGram g (f ∘ D) z 1 1) =ᶠ[𝓝 (D.symm p)] U ∘ D := by
    filter_upwards [hpair 0 0, hpair 1 1] with z h0 h1
    rw [h0, h1, hfac0, hfac1, hss, his]
    rfl
  have hC : (fun z => -2 * m60AreaGram g (f ∘ D) z 0 1) =ᶠ[𝓝 (D.symm p)]
      W ∘ D := by
    filter_upwards [hpair 0 1] with z h01
    rw [h01, hfac0, hfac1, mul_inv_cancel₀ hs, one_mul]
    rfl
  have hfp := hf.contMDiffAt (hO.mem_nhds hp)
  have hU : DifferentiableAt ℝ U p :=
    ((m64AreaGram_entry_contDiffAt (g := g) hfp 0 0).differentiableAt (by simp)).const_mul r |>.sub
      (((m64AreaGram_entry_contDiffAt (g := g) hfp 1 1).differentiableAt (by simp)).const_mul r⁻¹)
  have hW : DifferentiableAt ℝ W p :=
    ((m64AreaGram_entry_contDiffAt (g := g) hfp 0 1).differentiableAt (by simp)).const_mul (-2)
  have hd (F : LoopPlane → ℝ) (hF : DifferentiableAt ℝ F p) (i : Fin 2) :
      fderiv ℝ (F ∘ D) (D.symm p) (e i) =
        m64SourceScaleFactor s i * fderiv ℝ F p (e i) := by
    have hF' : DifferentiableAt ℝ F (D (D.symm p)) := by
      simpa only [D.apply_symm_apply] using hF
    rw [fderiv_comp (D.symm p) hF' D.differentiableAt, D.fderiv,
      ContinuousLinearMap.comp_apply]
    have hbase : D (e i) = m64SourceScaleFactor s i • e i := by
      simpa only [e, EuclideanSpace.basisFun_apply] using m64SourceScale_basis s hs i
    change fderiv ℝ F (D (D.symm p)) (D (e i)) = _
    rw [hbase, map_smul, D.apply_symm_apply]
    rfl
  change fderiv ℝ _ (D.symm p) (e 0) = _ ∧
    fderiv ℝ _ (D.symm p) (e 1) = _ at hcr
  rw [hA.fderiv_eq (𝕜 := ℝ), hC.fderiv_eq (𝕜 := ℝ),
    hd U hU 0, hd U hU 1, hd W hW 0, hd W hW 1] at hcr
  rw [hfac0, hfac1] at hcr
  change fderiv ℝ U p (e 0) = r⁻¹ * fderiv ℝ W p (e 1) ∧
    fderiv ℝ U p (e 1) = -r * fderiv ℝ W p (e 0)
  rw [← hs2]
  constructor
  · have h := hcr.1
    field_simp [hs] at h ⊢
    nlinarith only [h]
  · have h := hcr.2
    field_simp [hs] at h
    nlinarith only [h]

end PoincareConjecture
