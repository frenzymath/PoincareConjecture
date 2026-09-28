import PoincareConjecture.Proofs.M76.Mathlib.CoreRadialCompression
import Mathlib.Topology.OpenPartialHomeomorph.Constructions










set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem exists_compression_fixing_core (x : E) {U : Set E}
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ e : OpenPartialHomeomorph E E, e.source = univ ∧ e.target ⊆ U ∧
      ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ EqOn e id V := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hr2 : 0 < r / 2 := by positivity
  let F : E ≃ₜ E := (Homeomorph.smulOfNeZero (r / 2) hr2.ne').trans (Homeomorph.addRight x)
  have hF (z : E) : F z = (r / 2) • z + x := rfl
  have hdist (z : E) : dist (F z) x = (r / 2) * ‖z‖ := by
    rw [hF, dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr2]
  let e := F.symm.transOpenPartialHomeomorph
    ((coreCompression : OpenPartialHomeomorph E E).transHomeomorph F)
  refine ⟨e, ?_, ?_, F '' ball 0 1, F.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · change F.symm ⁻¹' univ = univ
    exact preimage_univ
  · intro y hy
    change F.symm y ∈ ball (0 : E) 2 at hy
    apply hball
    rw [mem_ball]
    have hn : ‖F.symm y‖ < 2 := mem_ball_zero_iff.mp hy
    have he : dist y x = (r / 2) * ‖F.symm y‖ := by
      simpa only [F.apply_symm_apply] using hdist (F.symm y)
    rw [he]
    nlinarith
  · exact ⟨0, by simp, by simp [hF]⟩
  · rintro z ⟨w, hw, rfl⟩
    change F (NormedSpace.coreCompression (F.symm (F w))) = F w
    rw [F.symm_apply_apply,
      NormedSpace.coreCompression_of_norm_le_one (mem_ball_zero_iff.mp hw).le]

variable {X : Type*} [TopologicalSpace X]




theorem exists_compression_in_chart (C : OpenPartialHomeomorph X E)
    (hCt : C.target = univ) {x : X} (hx : x ∈ C.source)
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ e : OpenPartialHomeomorph X X, e.source = C.source ∧ e.target ⊆ U ∧
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ EqOn e id V := by
  have hCU : IsOpen (C '' (C.source ∩ U)) := C.isOpen_image_source_inter hU
  obtain ⟨f, hfs, hft, V, hV, hxV, hfix⟩ :=
    exists_compression_fixing_core (C x) hCU ⟨x, ⟨hx, hxU⟩, rfl⟩
  let e := C.trans (f.trans C.symm)
  have hinner : (f.trans C.symm).source = univ := by
    rw [trans_source, symm_source, hCt, preimage_univ, inter_univ, hfs]
  have heS : e.source = C.source := by
    rw [trans_source, hinner, preimage_univ, inter_univ]
  refine ⟨e, heS, ?_, C.source ∩ C ⁻¹' V, C.isOpen_inter_preimage hV,
    ⟨hx, hxV⟩, ?_⟩
  · intro y hy
    have hfCx : f (C (e.symm y)) ∈ C '' (C.source ∩ U) :=
      hft (f.map_source (by rw [hfs]; trivial))
    obtain ⟨u, ⟨hus, huU⟩, hu⟩ := hfCx
    have heu : e (e.symm y) = u := by
      change C.symm (f (C (e.symm y))) = u
      rw [← hu, C.left_inv hus]
    have hyu : y = u := (e.right_inv hy).symm.trans heu
    exact hyu.symm ▸ huU
  · intro z hz
    change C.symm (f (C z)) = z
    calc
      C.symm (f (C z)) = C.symm (C z) := congrArg C.symm (hfix hz.2)
      _ = z := C.left_inv hz.1

end OpenPartialHomeomorph
