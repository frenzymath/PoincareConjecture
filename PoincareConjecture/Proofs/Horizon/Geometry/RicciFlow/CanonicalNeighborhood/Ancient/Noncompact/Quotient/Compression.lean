import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.CoreTopology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}



noncomputable def oddLineMap (C : M27TwistedSphereLineFlowCertificate K)
    (f : ℝ → ℝ) (x : M) : M :=
  let p := Classical.choose (C.cover_surjective x)
  C.cover (p.1, f p.2)

theorem oddLineMap_cover (C : M27TwistedSphereLineFlowCertificate K)
    {f : ℝ → ℝ} (hf : Function.Odd f) (p : UnitTwoSphere × ℝ) :
    C.oddLineMap f (C.cover p) = C.cover (p.1, f p.2) := by
  let q := Classical.choose (C.cover_surjective (C.cover p))
  have hq : C.cover q = C.cover p := Classical.choose_spec (C.cover_surjective (C.cover p))
  change C.cover (q.1, f q.2) = C.cover (p.1, f p.2)
  rcases (C.cover_fibers q p).mp hq with hp | hp
  · exact congrArg (fun z : UnitTwoSphere × ℝ => C.cover (z.1, f z.2)) hp.symm
  · apply (C.cover_fibers _ _).mpr
    right
    rw [hp]
    change (-q.1, f (-q.2)) = (-q.1, -f q.2)
    rw [hf q.2]



theorem contMDiffAt_oddLineMap (C : M27TwistedSphereLineFlowCertificate K)
    {f : ℝ → ℝ} (hf : Function.Odd f) (p : UnitTwoSphere × ℝ)
    (hf_smooth : ContDiffAt ℝ ∞ f p.2) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (C.oddLineMap f) (C.cover p) := by
  let hlocal := C.cover_local_diffeomorph p
  let e := hlocal.localInverse
  have hleft : e (C.cover p) = p :=
    hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  have hprod : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ∞ (fun q : UnitTwoSphere × ℝ => (q.1, f q.2)) p :=
    contMDiffAt_fst.prodMk (hf_smooth.contMDiffAt.comp p contMDiffAt_snd)
  have hcover := C.cover_local_diffeomorph.contMDiff.contMDiffAt.comp p hprod
  have hcomp := hcover.comp_of_eq hlocal.localInverse_contMDiffAt hleft
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hlocal.localInverse_mem_source] with y hy
  change C.oddLineMap f y = C.cover ((e y).1, f (e y).2)
  rw [← C.oddLineMap_cover hf (e y), hlocal.localInverse_right_inv hy]

private noncomputable def compressLine (r s : ℝ) : ℝ :=
  (2 * r / Real.pi) * Real.arctan s

private noncomputable def expandLine (r s : ℝ) : ℝ :=
  Real.tan (s / (2 * r / Real.pi))

private theorem compressLine_odd (r : ℝ) : Function.Odd (compressLine r) := by
  intro s
  simp [compressLine, Real.arctan_neg]

private theorem expandLine_odd (r : ℝ) : Function.Odd (expandLine r) := by
  intro s
  simp only [expandLine, neg_div, Real.tan_neg]

private theorem compression_scale_mul (r : ℝ) :
    (2 * r / Real.pi) * (Real.pi / 2) = r := by
  field_simp

private theorem compressLine_mem {r : ℝ} (hr : 0 < r) (s : ℝ) :
    compressLine r s ∈ Ioo (-r) r := by
  have ha : 0 < 2 * r / Real.pi := div_pos (by positivity) Real.pi_pos
  have hlo := mul_lt_mul_of_pos_left (Real.arctan_mem_Ioo s).1 ha
  have hhi := mul_lt_mul_of_pos_left (Real.arctan_mem_Ioo s).2 ha
  have hs := compression_scale_mul r
  constructor <;> dsimp only [compressLine] <;> nlinarith

private theorem expansion_argument_mem {r s : ℝ} (hr : 0 < r)
    (hs : s ∈ Ioo (-r) r) :
    s / (2 * r / Real.pi) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have ha : 0 < 2 * r / Real.pi := div_pos (by positivity) Real.pi_pos
  have hscale := compression_scale_mul r
  constructor
  · rw [lt_div_iff₀ ha]
    nlinarith [hs.1]
  · rw [div_lt_iff₀ ha]
    nlinarith [hs.2]

private theorem expandLine_compressLine {r : ℝ} (hr : 0 < r) (s : ℝ) :
    expandLine r (compressLine r s) = s := by
  have ha : 2 * r / Real.pi ≠ 0 := ne_of_gt (div_pos (by positivity) Real.pi_pos)
  simp only [expandLine, compressLine, mul_div_cancel_left₀ _ ha, Real.tan_arctan]

private theorem compressLine_expandLine {r s : ℝ} (hr : 0 < r)
    (hs : s ∈ Ioo (-r) r) : compressLine r (expandLine r s) = s := by
  have ha : 2 * r / Real.pi ≠ 0 := ne_of_gt (div_pos (by positivity) Real.pi_pos)
  have harg := expansion_argument_mem hr hs
  rw [compressLine, expandLine, Real.arctan_tan harg.1 harg.2]
  exact mul_div_cancel₀ _ ha

private theorem contDiff_compressLine (r : ℝ) : ContDiff ℝ ∞ (compressLine r) :=
  contDiff_const.mul Real.contDiff_arctan

private theorem contDiffAt_expandLine {r s : ℝ} (hr : 0 < r)
    (hs : s ∈ Ioo (-r) r) : ContDiffAt ℝ ∞ (expandLine r) s := by
  apply (Real.contDiffAt_tan.mpr
    (Real.cos_pos_of_mem_Ioo (expansion_argument_mem hr hs)).ne').comp s
  exact contDiffAt_id.div_const _



noncomputable def slabCapModel (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 < r) :
    CapModelEquivalence .puncturedProjective C.puncture
      (C.cover '' (univ ×ˢ Ioo (-r) r)) where
  model := M
  model_topology := inferInstance
  model_charted := inferInstance
  model_manifold := inferInstance
  standard_model := C.projective_topology.trans Homeomorph.ulift.symm
  standard_smooth := ⟨C.projective_smooth_cover⟩
  forward := C.oddLineMap (expandLine r)
  inverse := C.oddLineMap (compressLine r)
  inverse_mem := by
    intro x
    obtain ⟨p, rfl⟩ := C.cover_surjective x
    rw [C.oddLineMap_cover (compressLine_odd r)]
    exact ⟨(p.1, compressLine r p.2), ⟨mem_univ _, compressLine_mem hr _⟩, rfl⟩
  left_inverse := by
    rintro _ ⟨p, hp, rfl⟩
    rw [C.oddLineMap_cover (expandLine_odd r), C.oddLineMap_cover (compressLine_odd r)]
    simp only [compressLine_expandLine hr hp.2, Prod.eta]
  right_inverse := by
    intro x
    obtain ⟨p, rfl⟩ := C.cover_surjective x
    rw [C.oddLineMap_cover (compressLine_odd r), C.oddLineMap_cover (expandLine_odd r)]
    simp only [expandLine_compressLine hr, Prod.eta]
  forward_smooth := by
    rintro _ ⟨p, hp, rfl⟩
    exact (C.contMDiffAt_oddLineMap (expandLine_odd r) p
      (contDiffAt_expandLine hr hp.2)).contMDiffWithinAt
  inverse_smooth := by
    intro x _
    obtain ⟨p, rfl⟩ := C.cover_surjective x
    exact (C.contMDiffAt_oddLineMap (compressLine_odd r) p
      (contDiff_compressLine r).contDiffAt).contMDiffWithinAt

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
