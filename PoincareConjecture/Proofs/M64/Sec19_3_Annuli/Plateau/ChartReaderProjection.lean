import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ChartReaderMetric

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64ChartReadable_local_projection
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (p : M) :
    ∃ (U : Set M) (P : M → E →L[ℝ] E), IsOpen U ∧ p ∈ U ∧ ContinuousOn P U ∧
      (∀ q ∈ U, ∀ w, P q (mfderiv (𝓡 n) (𝓡 m) e q w) = mfderiv (𝓡 n) (𝓡 m) e q w) ∧
      ∀ q ∈ U, ∀ w, P q w ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) := by
  obtain ⟨b, hb, L, hL⟩ := hread p
  let c := chartAt (EuclideanSpace ℝ (Fin n)) b
  have hb' : p ∈ c.source := by simpa only [extChartAt_source] using hb
  have hL' : (L ∘ e) =ᶠ[𝓝 p] c := by
    change (fun q => L (e q)) =ᶠ[𝓝 p] c
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] using hL
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp
    (inter_mem (c.open_source.mem_nhds hb') hL')
  let P : M → E →L[ℝ] E := fun q => (fderiv ℝ (e ∘ c.symm) (c q)).comp L
  have hc : c.MDifferentiable (𝓡 n) (𝓡 n) := mdifferentiable_chart b
  have hce (q : M) (hq : q ∈ U) :
      ContDiffAt ℝ 1 (e ∘ c.symm) (c q) := by
    have hi : ContMDiffAt (𝓡 n) (𝓡 n) 1 c.symm (c q) :=
      (contMDiffOn_chart_symm : ContMDiffOn (𝓡 n) (𝓡 n) 1 c.symm c.target).contMDiffAt
        (c.open_target.mem_nhds (c.map_source (hUsub hq).1))
    exact contMDiffAt_iff_contDiffAt.mp ((he _).comp _ hi)
  have hde (q : M) (hq : q ∈ U) : fderiv ℝ (e ∘ c.symm) (c q) =
      (mfderiv (𝓡 n) (𝓡 m) e q).comp (mfderiv (𝓡 n) (𝓡 n) c.symm (c q)) := by
    have hh := mfderiv_comp (c q) ((he _).mdifferentiableAt (by simp))
      (hc.mdifferentiableAt_symm (c.map_source (hUsub hq).1))
    rw [mfderiv_eq_fderiv, c.left_inv (hUsub hq).1] at hh
    exact hh
  have hLe (q : M) (hq : q ∈ U) : L.comp (mfderiv (𝓡 n) (𝓡 m) e q) =
      mfderiv (𝓡 n) (𝓡 n) c q := by
    have hlocal : (L ∘ e) =ᶠ[𝓝 q] c := by
      filter_upwards [hUopen.mem_nhds hq] with y hy
      exact (hUsub hy).2
    have hh := hlocal.mfderiv_eq (I := 𝓡 n) (I' := 𝓡 n)
    rw [mfderiv_comp q L.differentiableAt.mdifferentiableAt
      ((he q).mdifferentiableAt (by simp)), mfderiv_eq_fderiv, L.fderiv] at hh
    exact hh
  refine ⟨U, P, hUopen, hpU, ?_, ?_, ?_⟩
  · apply continuousOn_clm_apply.mpr
    intro w q hq
    exact (((hce q hq).continuousAt_fderiv (by simp)).comp
      (c.continuousOn.continuousAt (c.open_source.mem_nhds (hUsub hq).1))).clm_apply
        continuousAt_const |>.continuousWithinAt
  · intro q hq w
    change fderiv ℝ (e ∘ c.symm) (c q) (L (mfderiv (𝓡 n) (𝓡 m) e q w)) = _
    rw [hde q hq]
    change mfderiv (𝓡 n) (𝓡 m) e q
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c q) ((L.comp (mfderiv (𝓡 n) (𝓡 m) e q)) w)) = _
    rw [hLe q hq]
    have hid := congrArg (fun T => T w) (hc.symm_comp_deriv (hUsub hq).1)
    change mfderiv (𝓡 n) (𝓡 n) c.symm (c q) (mfderiv (𝓡 n) (𝓡 n) c q w) = w at hid
    exact congrArg (mfderiv (𝓡 n) (𝓡 m) e q) hid
  · intro q hq w
    refine ⟨mfderiv (𝓡 n) (𝓡 n) c.symm (c q) (L w), ?_⟩
    change _ = fderiv ℝ (e ∘ c.symm) (c q) (L w)
    rw [hde q hq]
    rfl

end PoincareConjecture
