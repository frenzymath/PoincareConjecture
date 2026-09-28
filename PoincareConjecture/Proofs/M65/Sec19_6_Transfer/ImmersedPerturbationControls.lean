import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaMotion
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.BumpFunction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

theorem exists_smooth_field [T2Space M] (p : M) (v : TangentSpace (𝓡 3) p) :
    ∃ V : (y : M) → TangentSpace (𝓡 3) y,
      ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
        (fun y => (⟨y, V y⟩ : TangentBundle (𝓡 3) M)) ∧ V p = v := by
  let Z := FiberBundle.extend LoopAmbient v
  obtain ⟨U, hU, hZU⟩ := FiberBundle.exists_contMDiffOn_extend
    (I := 𝓡 3) (F := LoopAmbient) (k := (∞ : WithTop ℕ∞)) v
  obtain ⟨W, hWU, hW, hpW⟩ := mem_nhds_iff.mp hU
  obtain ⟨chi, -, hchi⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 3) p).mem_iff.mp (hW.mem_nhds hpW)
  refine ⟨fun y => chi y • Z y, ?_, ?_⟩
  · exact ContMDiffOn.smul_section_of_tsupport (u := W) (s := Z)
      (ψ := chi.toFun) chi.contMDiff.contMDiffOn hW hchi (hZU.mono hWU)
  · simp only [chi.eq_one, one_smul, Z, FiberBundle.extend_apply_self]

theorem exists_smooth_motion_with_velocity [T2Space M] [CompactSpace M]
    (p : M) (v : TangentSpace (𝓡 3) p) :
    ∃ (d : ℝ) (Phi : M × ℝ → M), 0 < d ∧
      ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ Phi
        (univ ×ˢ Ioo (-d) d) ∧
      (∀ y, Phi (y, 0) = y) ∧
      curveVelocity (n := 3) (fun r => Phi (p, r)) 0 = v := by
  obtain ⟨V, hV, hpV⟩ := exists_smooth_field p v
  have htime : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : ℝ × M => (⟨z.2, V z.2⟩ : TangentBundle (𝓡 3) M)) (univ ×ˢ univ) :=
    (hV.comp contMDiff_snd).contMDiffOn
  obtain ⟨G, d, Phi, _hG, hcover, hd, _hT, hPhi, hzero, hvel⟩ :=
    M65Filling.compact_motion (fun _ => V) univ isOpen_univ htime 0 (mem_univ _)
      univ isCompact_univ ⟨p, mem_univ _⟩
  have hG : G = univ := univ_subset_iff.mp hcover
  subst G
  refine ⟨d, Phi, hd, hPhi, fun y => hzero y (mem_univ _), ?_⟩
  have hv := (hvel p (mem_univ _) 0 ⟨neg_neg_of_pos hd, hd⟩).2
  exact hv.trans ((congrArg (fun y => (V y : LoopAmbient)) (hzero p (mem_univ _))).trans hpV)

omit [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] in

theorem exists_source_bump (x y : LoopCircle) (hxy : x ≠ y) :
    ∃ beta : LoopPlane → ℝ, ContDiff ℝ ∞ beta ∧
      (∀ z, beta z ∈ Icc (0 : ℝ) 1) ∧ beta x = 1 ∧ beta y = 0 := by
  have hdist : 0 < dist (y : LoopPlane) (x : LoopPlane) :=
    dist_pos.mpr (fun h => hxy (Subtype.ext h.symm))
  let beta : ContDiffBump (x : LoopPlane) := {
    rIn := dist (y : LoopPlane) (x : LoopPlane) / 4
    rOut := dist (y : LoopPlane) (x : LoopPlane) / 2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  refine ⟨beta, beta.contDiff, fun z => ⟨beta.nonneg, beta.le_one⟩, ?_, ?_⟩
  · exact beta.one_of_mem_closedBall (Metric.mem_closedBall_self beta.rIn_pos.le)
  · exact beta.zero_of_le_dist (by dsimp [beta]; linarith)

end PoincareConjecture.M65Perturbation
