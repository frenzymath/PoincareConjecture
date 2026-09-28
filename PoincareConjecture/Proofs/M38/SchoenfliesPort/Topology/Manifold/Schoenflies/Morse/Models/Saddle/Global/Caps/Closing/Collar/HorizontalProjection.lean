import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.HorizontalChart
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.TerminalProjection

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_fst_projection_chart
    {J : E2 → E2 × Real} {V : Set E2} (hV : IsOpen V)
    (hVc : sphere (0 : E2) 1 ⊆ V) (hJ : ContDiffOn Real ∞ J V)
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hRc : R '' sphere (0 : E2) 1 = sphere (0 : E2) 1)
    (hJc : ∀ q ∈ sphere (0 : E2) 1, J q = (R q, 0))
    (hJi : ∀ q ∈ sphere (0 : E2) 1, Injective (fderiv Real J q))
    (hJn : ∀ q ∈ sphere (0 : E2) 1, fderiv Real (fun x => (J x).2) q = 0) :
    ∃ T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      sphere (0 : E2) 1 ⊆ T.source ∧
      T '' sphere (0 : E2) 1 = sphere (0 : E2) 1 ∧
      T.source ⊆ V ∧ ∀ x ∈ T.source, T x = (J x).1 := by
  let k : E2 → E2 := fun x => (J x).1
  have hk : ContDiffOn Real ∞ k V := hJ.fst
  have hki (q : E2) (hq : q ∈ sphere (0 : E2) 1) :
      Injective (fderiv Real k q) := by
    have hd := (hJ.contDiffAt (hV.mem_nhds (hVc hq))).differentiableAt (by simp)
    intro u v huv
    apply hJi q hq
    apply Prod.ext
    · change fderiv Real (fun x => (J x).1) q u =
        fderiv Real (fun x => (J x).1) q v at huv
      rw [hd.hasFDerivAt.fst.fderiv] at huv
      exact huv
    · have hn := hJn q hq
      rw [hd.hasFDerivAt.snd.fderiv] at hn
      have hu := congrArg (fun L : E2 →L[Real] Real => L u) hn
      have hv := congrArg (fun L : E2 →L[Real] Real => L v) hn
      exact hu.trans hv.symm
  obtain ⟨k₀, hk₀, _, hk₀eq⟩ := Poincare.Parabolic.Interior.exists_compact_smooth_extension
    (isCompact_sphere (0 : E2) 1) hV hVc hk
  have hlocal (q : E2) (hq : q ∈ sphere (0 : E2) 1) :
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ k q := by
    have hi : Injective (fderiv Real k₀ q) := by
      rw [(hk₀eq q hq).fderiv_eq]
      exact hki q hq
    exact (localDiffeomorphAt_of_smooth_bijective_derivative hk₀
      ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).congr_of_eventuallyEq
        (hk₀eq q hq).symm
  have hkc : EqOn k R (sphere (0 : E2) 1) := fun q hq => congrArg Prod.fst (hJc q hq)
  obtain ⟨n, hn, _, hnk, hns, hnsi⟩ := Poincare.exists_openPartialHomeomorph_of_injOn_compact
    (isCompact_sphere (0 : E2) 1)
    (show InjOn k (sphere (0 : E2) 1) from fun x hx y hy heq =>
      R.injective ((hkc hx).symm.trans (heq.trans (hkc hy)))) hlocal
  let T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    { n.restrOpen V hV with
      contMDiffOn_toFun := hns.mono inter_subset_left
      contMDiffOn_invFun := hnsi.mono inter_subset_left }
  refine ⟨T, (fun x hx => ⟨hn hx, hVc hx⟩), ?_, inter_subset_right,
    fun x hx => hnk hx.1⟩
  calc
    T '' sphere (0 : E2) 1 = R '' sphere (0 : E2) 1 :=
      image_congr (fun x hx => (hnk (hn hx)).trans (hkc hx))
    _ = _ := hRc

open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

def actualCapPhysicalCoordinates (data : TerminalSaddleData M P p e)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (i : Fin 3) (x : E2) : E3 :=
  data.toTerminalSaddleGeometry.filledModel (actualCapModelCoordinates data H i x)

theorem actualCapPhysicalCoordinates_eq (data : TerminalSaddleData M P p e)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (i : Fin 3) (x : E2) :
    actualCapPhysicalCoordinates data H i x =
      data.toTerminalSaddleGeometry.flatten.symm
        (H (data.toTerminalSaddleGeometry.flatten (g (data.actualDisk i x)))) := by
  simp only [actualCapPhysicalCoordinates, actualCapModelCoordinates,
    Diffeomorph.apply_symm_apply]

theorem exists_actual_horizontal_projection_in_chart
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (i : Fin 3)
    (D : PartialDiffeomorph 𝓘(Real, E2 × Real) (𝓡 3) (E2 × Real) E3 ∞)
    (hDs : sphere (0 : E2) 1 ×ˢ ({0} : Set Real) ⊆ D.source)
    (hDq : ∀ q ∈ sphere (0 : E2) 1,
      D (q, 0) = data.toTerminalSaddleGeometry.filledModel (data.modelDisk i q))
    (hDn : ∀ z ∈ D.source,
      ‖data.toTerminalSaddleGeometry.filledModel.symm (D z)‖ = 1 + z.2) :
    ∃ T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      sphere (0 : E2) 1 ⊆ T.source ∧
      T '' sphere (0 : E2) 1 = sphere (0 : E2) 1 ∧
      T.source ⊆ (data.actualDisk i).source ∧
      ∀ x ∈ T.source, actualCapPhysicalCoordinates data H i x ∈ D.target ∧
        T x = (D.symm (actualCapPhysicalCoordinates data H i x)).1 := by
  let F := actualCapModelCoordinates data H i
  let A := actualCapPhysicalCoordinates data H i
  let J : E2 → E2 × Real := D.symm ∘ A
  have hF := contDiffOn_actualCapModelCoordinates data hg H i
  have hA : ContDiffOn Real ∞ A (data.actualDisk i).source :=
    (data.toTerminalSaddleGeometry.filledModel.contMDiff.comp_contMDiffOn hF.contMDiffOn).contDiffOn
  let V := (data.actualDisk i).source ∩ A ⁻¹' D.target
  have hV : IsOpen V := hA.continuousOn.isOpen_inter_preimage
    (data.actualDisk i).open_source D.open_target
  have hJ : ContDiffOn Real ∞ J V :=
    (D.contMDiffOn_invFun.comp (hA.contMDiffOn.mono inter_subset_left)
      (fun x hx => hx.2)).contDiffOn
  obtain ⟨R, hRc, hRb, hR⟩ :=
    exists_terminal_boundary_reparametrization data hg Φ χ H hH hχ hplanar hlabels i
  have hRcircle : R '' sphere (0 : E2) 1 = sphere (0 : E2) 1 := by
    rw [← closedBall_sdiff_ball, image_sdiff (f := (R : E2 → E2)) R.injective, hRc, hRb]
  have hAc (q : E2) (hq : q ∈ sphere (0 : E2) 1) : A q = D (R q, 0) := by
    rw [hDq (R q) (hRcircle ▸ mem_image_of_mem R hq)]
    have hh := congrArg data.toTerminalSaddleGeometry.flatten.symm (hR q hq)
    simp only [Diffeomorph.symm_apply_apply] at hh
    exact (actualCapPhysicalCoordinates_eq data H i q).trans hh.symm
  have hVc : sphere (0 : E2) 1 ⊆ V := by
    intro q hq
    refine ⟨data.actualDisk_source i (sphere_subset_closedBall hq), ?_⟩
    change A q ∈ D.target
    rw [hAc q hq]
    exact D.map_source (hDs ⟨hRcircle ▸ mem_image_of_mem R hq, rfl⟩)
  have hJc (q : E2) (hq : q ∈ sphere (0 : E2) 1) : J q = (R q, 0) := by
    change D.symm (A q) = _
    rw [hAc q hq]
    exact D.left_inv (hDs ⟨hRcircle ▸ mem_image_of_mem R hq, rfl⟩)
  have hJi (q : E2) (hq : q ∈ sphere (0 : E2) 1) :
      Injective (fderiv Real J q) := by
    have hqV := hVc hq
    have hFloc := hF.contDiffAt ((data.actualDisk i).open_source.mem_nhds hqV.1)
    have hAloc := hA.contDiffAt ((data.actualDisk i).open_source.mem_nhds hqV.1)
    have hDloc := D.symm.isLocalDiffeomorphAt (𝓡 3) 𝓘(Real, E2 × Real) ∞ hqV.2
    have hAi : Injective (mfderiv (𝓡 2) (𝓡 3) A q) := by
      change Injective (mfderiv (𝓡 2) (𝓡 3)
        (data.toTerminalSaddleGeometry.filledModel ∘ F) q)
      rw [mfderiv_comp q
        (data.toTerminalSaddleGeometry.filledModel.contMDiff.mdifferentiable (by simp) _)
        (hFloc.contMDiffAt.mdifferentiableAt (by simp))]
      apply (data.toTerminalSaddleGeometry.filledModel.mfderivToContinuousLinearEquiv
        (by simp) _).injective.comp
      rw [mfderiv_eq_fderiv]
      exact injective_fderiv_actualCapModelCoordinates data hg H i hqV.1
    have hi : Injective (mfderiv (𝓡 2) 𝓘(Real, E2 × Real) J q) := by
      rw [show J = D.symm ∘ A from rfl, mfderiv_comp q
        (hDloc.mdifferentiableAt (by simp))
        (hAloc.contMDiffAt.mdifferentiableAt (by simp))]
      exact (hDloc.mfderivToContinuousLinearEquiv (by simp)).injective.comp hAi
    simpa only [mfderiv_eq_fderiv, TangentSpace] using hi
  have hJnormal (x : E2) (hx : x ∈ V) : (J x).2 = ‖F x‖ - 1 := by
    have hh := hDn (D.symm (A x)) (D.map_target hx.2)
    have hi : D (D.symm (A x)) = A x := D.right_inv hx.2
    rw [hi] at hh
    change ‖data.toTerminalSaddleGeometry.filledModel.symm
      (data.toTerminalSaddleGeometry.filledModel (F x))‖ = 1 + (J x).2 at hh
    rw [Diffeomorph.symm_apply_apply] at hh
    linarith
  obtain ⟨r, hr, _, houter, _⟩ :=
    exists_actual_terminal_sphere_projection data hg Φ χ H hH hχ hplanar i
  have hJn (q : E2) (hq : q ∈ sphere (0 : E2) 1) :
      fderiv Real (fun x => (J x).2) q = 0 := by
    have heq : (fun x => (J x).2) =ᶠ[𝓝 q] (fun x => ‖F x‖ - 1) := by
      filter_upwards [hV.mem_nhds (hVc hq)] with x hx
      exact hJnormal x hx
    rw [heq.fderiv_eq]
    have hqouter : q ∈ closedBall (0 : E2) r \ ball 0 1 :=
      ⟨closedBall_subset_closedBall hr.le (sphere_subset_closedBall hq),
        fun hb => (ne_of_lt (mem_ball.mp hb)) (mem_sphere.mp hq)⟩
    have hFnz : F q ≠ 0 := ne_zero_of_mem_unit_sphere ⟨F q, houter hqouter⟩
    apply fderiv_eq_zero_of_eqOn_outer_annulus hr
      (fun x hx => sub_eq_zero.mpr (mem_sphere_zero_iff_norm.mp (houter hx))) hq
    exact (((contDiffAt_norm Real hFnz).comp q
      (hF.contDiffAt ((data.actualDisk i).open_source.mem_nhds (hVc hq).1))).sub
        contDiffAt_const).differentiableAt (by simp)
  obtain ⟨T, hTc, hTi, hTs, hTk⟩ :=
    exists_fst_projection_chart hV hVc hJ R hRcircle hJc hJi hJn
  exact ⟨T, hTc, hTi, fun x hx => (hTs hx).1,
    fun x hx => ⟨(hTs hx).2, hTk x hx⟩⟩

theorem exists_actual_terminal_horizontal_graph
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (i : Fin 3) :
    ∃ c : Real, (c = data.ends.lowerCut ∨ c = data.ends.upperCut) ∧
      ∃ D : PartialDiffeomorph 𝓘(Real, E2 × Real) (𝓡 3) (E2 × Real) E3 ∞,
        sphere (0 : E2) 1 ×ˢ ({0} : Set Real) ⊆ D.source ∧
        (∀ q ∈ sphere (0 : E2) 1,
          D (q, 0) = data.toTerminalSaddleGeometry.filledModel (data.modelDisk i q)) ∧
        (∀ z ∈ D.source, inner Real (M.v : E3) (D z) = c + ‖z.1‖ - 1 ∧
          ‖data.toTerminalSaddleGeometry.filledModel.symm (D z)‖ = 1 + z.2) ∧
        ∃ (T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (a : E2 → Real),
          sphere (0 : E2) 1 ⊆ T.source ∧
          T '' sphere (0 : E2) 1 = sphere (0 : E2) 1 ∧
          T.source ⊆ (data.actualDisk i).source ∧
          ContDiffOn Real ∞ a T.target ∧
          EqOn a (fun _ => 0) (sphere (0 : E2) 1) ∧
          (∀ y ∈ T.target, (y, a y) ∈ D.source ∧
            actualCapPhysicalCoordinates data H i (T.symm y) = D (y, a y)) ∧
          (∀ y ∈ T.target, actualCapModelCoordinates data H i (T.symm y) ∈
            sphere (0 : E3) 1 → a y = 0) ∧
          ∃ V : Set E2, IsOpen V ∧ sphere (0 : E2) 1 ⊆ V ∧ V ⊆ T.target ∧
            (∀ y ∈ V, (y, 0) ∈ D.source) ∧
            ∀ y ∈ V, data.toTerminalSaddleGeometry.flatten (D (y, 0)) ∈
              data.toTerminalSaddleGeometry.modelBand → a y = 0 := by
  obtain ⟨c, hc, D, hDs, hDq, _, hDh⟩ := exists_terminal_model_horizontal_chart data i
  obtain ⟨T, hTc, hTi, hTs, hT⟩ := exists_actual_horizontal_projection_in_chart
    data hg Φ χ H hH hχ hplanar hlabels i D hDs hDq (fun z hz => (hDh z hz).2)
  let A := actualCapPhysicalCoordinates data H i
  let a : E2 → Real := fun y => (D.symm (A (T.symm y))).2
  have hA : ContDiffOn Real ∞ A (data.actualDisk i).source :=
    (data.toTerminalSaddleGeometry.filledModel.contMDiff.comp_contMDiffOn
      (contDiffOn_actualCapModelCoordinates data hg H i).contMDiffOn).contDiffOn
  have ha : ContDiffOn Real ∞ a T.target := by
    intro y hy
    have hAloc := hA.contDiffAt ((data.actualDisk i).open_source.mem_nhds
      (hTs (T.map_target hy)))
    have hTloc := T.contMDiffOn_invFun.contDiffOn.contDiffAt (T.open_target.mem_nhds hy)
    have hDloc := D.contMDiffOn_invFun.contDiffOn.contDiffAt
      (D.open_target.mem_nhds (hT _ (T.map_target hy)).1)
    exact ((hDloc.comp y (hAloc.comp y hTloc)).snd).contDiffWithinAt
  have hcoord (y : E2) (hy : y ∈ T.target) : D.symm (A (T.symm y)) = (y, a y) := by
    apply Prod.ext
    · exact (hT _ (T.map_target hy)).2.symm.trans (T.right_inv hy)
    · rfl
  have hgraph (y : E2) (hy : y ∈ T.target) : (y, a y) ∈ D.source ∧
      A (T.symm y) = D (y, a y) := by
    have hs : D.symm (A (T.symm y)) ∈ D.source :=
      D.map_target (hT _ (T.map_target hy)).1
    have hi : D (D.symm (A (T.symm y))) = A (T.symm y) :=
      D.right_inv (hT _ (T.map_target hy)).1
    rw [hcoord y hy] at hs hi
    exact ⟨hs, hi.symm⟩
  have hzero (y : E2) (hy : y ∈ T.target)
      (hsphere : actualCapModelCoordinates data H i (T.symm y) ∈ sphere (0 : E3) 1) :
      a y = 0 := by
    have hh := (hDh (y, a y) (hgraph y hy).1).2
    rw [← (hgraph y hy).2] at hh
    change ‖data.toTerminalSaddleGeometry.filledModel.symm
      (data.toTerminalSaddleGeometry.filledModel
        (actualCapModelCoordinates data H i (T.symm y)))‖ = 1 + a y at hh
    rw [Diffeomorph.symm_apply_apply, mem_sphere_zero_iff_norm.mp hsphere] at hh
    linarith
  have hac : EqOn a (fun _ => 0) (sphere (0 : E2) 1) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hTi.symm ▸ hy
    apply hzero _ (T.map_source (hTc hx))
    have hi : T.symm (T x) = x := T.left_inv (hTc hx)
    rw [hi]
    obtain ⟨r, hr, _, houter, _⟩ :=
      exists_actual_terminal_sphere_projection data hg Φ χ H hH hχ hplanar i
    exact houter ⟨closedBall_subset_closedBall hr.le (sphere_subset_closedBall hx),
      fun hb => (ne_of_lt (mem_ball.mp hb)) (mem_sphere.mp hx)⟩
  refine ⟨c, hc, D, hDs, hDq, hDh, T, a, hTc, hTi, hTs, ha, hac, hgraph, hzero, ?_⟩
  let s : S2 → E3 := H ∘ data.toTerminalSaddleGeometry.flatten ∘ g
  let n : E2 → E3 := fun y => data.toTerminalSaddleGeometry.flatten (D (y, 0))
  have hs : Topology.IsEmbedding s := H.toHomeomorph.isEmbedding.comp
    (data.toTerminalSaddleGeometry.flatten.toHomeomorph.isEmbedding.comp
      (M.tree.embedding_of_mem_leaves hg).isEmbedding)
  obtain ⟨U, hU, hchartU, hcover⟩ := exists_surface_neighborhood_in_chart
    hs (data.actualDisk i) T.open_source hTs
  have hband := terminal_band_image data Φ χ H hH hχ hplanar
  have hbandrange : data.toTerminalSaddleGeometry.modelBand ⊆ range s := by
    rw [show range s = H '' (data.toTerminalSaddleGeometry.flatten '' range g) by
      simp only [s, range_comp], ← hband]
    apply image_mono
    rw [data.actual_decomposition]
    exact subset_union_left
  let W : Set E2 := T.target ∩ (fun y => (y, (0 : Real))) ⁻¹' D.source
  have hW : IsOpen W := T.open_target.inter
    (D.open_source.preimage (continuous_id.prodMk continuous_const))
  have hn : ContinuousOn n W := by
    apply data.toTerminalSaddleGeometry.flatten.toHomeomorph.continuous.comp_continuousOn
    exact D.toOpenPartialHomeomorph.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun y hy => hy.2)
  let V := W ∩ n ⁻¹' U
  have hV : IsOpen V := hn.isOpen_inter_preimage hW hU
  have hVc : sphere (0 : E2) 1 ⊆ V := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hTi.symm ▸ hy
    have hyt : y ∈ T.target := hxy ▸ T.map_source (hTc hx)
    refine ⟨⟨hyt, hDs ⟨hy, rfl⟩⟩, ?_⟩
    have hi : T.symm y = x := hxy ▸ T.left_inv (hTc hx)
    have hg := (hgraph y hyt).2
    rw [hac hy, hi] at hg
    have heq : n y = s (data.actualDisk i x) := by
      change data.toTerminalSaddleGeometry.flatten (D (y, 0)) = _
      rw [← hg]
      change data.toTerminalSaddleGeometry.flatten (actualCapPhysicalCoordinates data H i x) = _
      rw [actualCapPhysicalCoordinates_eq]
      exact data.toTerminalSaddleGeometry.flatten.apply_symm_apply _
    change n y ∈ U
    rw [heq]
    exact hchartU (mem_image_of_mem (s ∘ data.actualDisk i) (hTc hx))
  refine ⟨V, hV, hVc, fun y hy => hy.1.1, fun y hy => hy.1.2, ?_⟩
  intro y hy hyband
  obtain ⟨x, hx, hxy⟩ := hcover ⟨hbandrange hyband, hy.2⟩
  have hAx : A x = D (y, 0) := by
    have hh := congrArg data.toTerminalSaddleGeometry.flatten.symm hxy
    change data.toTerminalSaddleGeometry.flatten.symm
      (H (data.toTerminalSaddleGeometry.flatten (g (data.actualDisk i x)))) =
        data.toTerminalSaddleGeometry.flatten.symm
          (data.toTerminalSaddleGeometry.flatten (D (y, 0))) at hh
    rw [Diffeomorph.symm_apply_apply] at hh
    exact (actualCapPhysicalCoordinates_eq data H i x).trans hh
  have hJx : D.symm (A x) = (y, 0) := by
    rw [hAx]
    exact D.left_inv hy.1.2
  have hTx : T x = y := (hT x hx).2.trans (congrArg Prod.fst hJx)
  have hinv : T.symm y = x := hTx ▸ T.left_inv hx
  change (D.symm (A (T.symm y))).2 = 0
  rw [hinv, hJx]

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
