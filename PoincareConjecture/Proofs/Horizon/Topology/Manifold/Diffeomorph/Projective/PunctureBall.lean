import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.Covering
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.RadialTransition











noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.StandardPuncturedProjectiveCover

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  {p : RealProjectiveThree} {U : Set M}
  (S : StandardPuncturedProjectiveCover M p U)



theorem exists_puncture_ball_avoiding_compact
    (a : UnitThreeSphere) (ha : Quotient.mk' a = p)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ b : OpenPartialHomeomorph E3 UnitThreeSphere,
      b.source = univ ∧ b 0 = a ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      Disjoint (b '' Metric.closedBall 0 1) (Neg.neg '' (b '' Metric.closedBall 0 1)) ∧
      ∀ x ∈ b '' Metric.closedBall 0 1, Quotient.mk' x ≠ p → S.cover x ∉ K := by
  let L := {x : UnitThreeSphere | Quotient.mk' x ≠ p ∧ S.cover x ∈ K}
  have hL : IsCompact L := S.isCompact_lift hK hKU
  have haL : a ∉ L := fun h => h.1 ha
  obtain ⟨V, W, hV, hW, haV, hnW, hVW⟩ :=
    t2_separation (ne_neg_of_mem_unit_sphere ℝ a)
  let O := V ∩ Neg.neg ⁻¹' W ∩ Lᶜ
  have hO : IsOpen O := (hV.inter (hW.preimage continuous_neg)).inter hL.isClosed.isOpen_compl
  have haO : a ∈ O := ⟨⟨haV, hnW⟩, haL⟩
  let e := (SphereCharts.radialSphereChart (-a)).symm
  have hes : e.source = univ := SphereCharts.radialSphereChart_target (-a)
  have he0 : e 0 = a := by simp [e]
  have hec : Continuous e := continuousOn_univ.mp (hes ▸ e.continuousOn)
  obtain ⟨r, hr, hrO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hO.preimage hec).mem_nhds (show (0 : E3) ∈ e ⁻¹' O by rwa [mem_preimage, he0]))
  let d := (Homeomorph.smulOfNeZero r hr.ne' : E3 ≃ₜ E3).toOpenPartialHomeomorph
  let b := d.trans e
  have hbs : b.source = univ := by simp [b, d, hes]
  have hb0 : b 0 = a := by change e (r • 0) = a; simpa using he0
  have hd : ContMDiff (𝓡 3) (𝓡 3) ∞ d := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : E3 => r • x)
    exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : E3 => r)).smul contDiff_id).contMDiff
  have hdi : ContMDiff (𝓡 3) (𝓡 3) ∞ d.symm := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : E3 => r⁻¹ • x)
    exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : E3 => r⁻¹)).smul contDiff_id).contMDiff
  have hbO : b '' Metric.closedBall 0 1 ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    change e (r • x) ∈ O
    apply hrO
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) hr.le).trans_eq (mul_one r)
  refine ⟨b, hbs, hb0,
    (SphereCharts.contMDiffOn_radialSphereChart_symm (-a)).comp hd.contMDiffOn inter_subset_right,
    hdi.comp_contMDiffOn
      ((SphereCharts.contMDiffOn_radialSphereChart (-a)).mono inter_subset_left), ?_, ?_⟩
  · apply hVW.mono (fun x hx => (hbO hx).1.1)
    rintro _ ⟨x, hx, rfl⟩
    exact (hbO hx).1.2
  · intro x hx hxp hxK
    exact (hbO hx).2 ⟨hxp, hxK⟩

end PoincareConjecture.StandardPuncturedProjectiveCover
