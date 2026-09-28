import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Orientation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.Persistence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientKappaSolution

open RicciFlow.Splitting Poincare.Geometry.RicciFlow.Harnack

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  (K : AncientKappaSolution 3 M) {b : ℝ} (hb : b ≤ 0)
  (x : M) (v w : TangentSpace (𝓡 3) x)
  (hv : (K.flow.metric b).inner x v v = 1)
  (hw : (K.flow.metric b).inner x w w = 1)
  (hvw : (K.flow.metric b).inner x v w = 0)
  (hzero : (K.flow.connection b).curvatureTensor x v w v w = 0)

include hb hv hw hvw hzero



theorem exists_ricci_null_vector_on_past_of_null_plane
    (t : ℝ) (ht : t ≤ b) (y : M) :
    ∃ z : TangentSpace (𝓡 3) y, z ≠ 0 ∧
      ∀ u, (K.flow.connection t).ricci y z u = 0 := by
  have hshift : (fun s : ℝ => s + b) '' Iic 0 ⊆ Iic 0 := by
    rintro _ ⟨s, hs, rfl⟩
    exact add_nonpos (show s ≤ 0 from hs) hb
  let F := K.flow.translate b hshift ordConnected_Iic
    (show (Iic (0 : ℝ)).Nontrivial from
      ⟨-1, by norm_num, 0, by simp, by norm_num⟩)
  have hop : ∀ s ≤ 0, ∀ p, (F.connection s).NonnegativeCurvatureOperator p := by
    intro s hs p
    exact K.nonnegative_curvature_operator (s + b) (add_nonpos hs hb) p
  have hv' : (F.metric 0).inner x v v = 1 := by
    simpa only [F, RicciFlow.translate, zero_add] using hv
  have hw' : (F.metric 0).inner x w w = 1 := by
    simpa only [F, RicciFlow.translate, zero_add] using hw
  have hvw' : (F.metric 0).inner x v w = 0 := by
    simpa only [F, RicciFlow.translate, zero_add] using hvw
  have hz' : (F.connection 0).curvatureTensor x v w v w = 0 := by
    change (K.flow.connection (0 + b)).curvatureTensor x v w v w = 0
    exact (congrArg (fun s : ℝ =>
      (K.flow.connection s).curvatureTensor x v w v w = 0) (zero_add b)).mpr hzero
  have hn := F.exists_ricci_null_vector_on_past_of_terminal_null_plane
    ricciFlowCurvatureTheory hop x v w hv' hw' hvw' hz'
    (t - b) (sub_nonpos.mpr ht) y
  change (∃ z : TangentSpace (𝓡 3) y, z ≠ 0 ∧
    ∀ u, (K.flow.connection (t - b + b)).ricci y z u = 0) at hn
  exact (congrArg (fun s : ℝ => ∃ z : TangentSpace (𝓡 3) y, z ≠ 0 ∧
    ∀ u, (K.flow.connection s).ricci y z u = 0) (sub_add_cancel t b)).mp hn


theorem ricciNullity_eq_one_on_past_of_null_plane
    (t : ℝ) (ht : t ≤ b) (y : M) :
    ricciNullity (K.flow.connection t) y = 1 := by
  have ht0 := ht.trans hb
  obtain ⟨p, hp⟩ := K.nonflat t ht0
  have hupper := (K.flow.connection t).ricciNullity_le_one_of_nonflat
    (ricciFlowCurvatureTheory.tensor_calculus 3 M _ _) p
    (K.nonnegative_curvature_operator t ht0 p) hp
  have hab : t - 1 < t := by linarith
  let F := restrictFlow K.flow
    (show Icc (t - 1) t ⊆ Iic 0 from fun _ hs => hs.2.trans ht0)
    ordConnected_Icc ⟨t - 1, ⟨le_rfl, hab.le⟩, t, ⟨hab.le, le_rfl⟩, hab.ne⟩
  have hsec : ∀ s ∈ Icc (t - 1) t, (F.connection s).NonnegativeSectionalCurvature := by
    intro s hs q a c
    exact (K.flow.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      q (K.nonnegative_curvature_operator s (hs.2.trans ht0) q) a c
  have hspace := ricciNullity_eq_on_positive_slice ricciFlowCurvatureTheory hab F hsec
    (show t ∈ Ioc (t - 1) t from ⟨hab, le_rfl⟩) y p
  change ricciNullity (K.flow.connection t) y = ricciNullity (K.flow.connection t) p
    at hspace
  have hpos : 0 < ricciNullity (K.flow.connection t) y := by
    obtain ⟨z, hz, hn⟩ := K.exists_ricci_null_vector_on_past_of_null_plane
      hb x v w hv hw hvw hzero t ht y
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨z, (mem_ricciKernel _ _ _).mpr hn⟩, ?_⟩
    intro heq
    exact hz (congrArg Subtype.val heq)
  omega



theorem ricciKernel_eq_on_past_of_null_plane
    (t : ℝ) (ht : t ≤ b) (y : M) :
    ricciKernel (K.flow.connection t) y = ricciKernel (K.flow.connection b) y := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) y) := by
    unfold TangentSpace
    infer_instance
  have hab : t - 1 < b := by linarith
  let F := restrictFlow K.flow
    (show Icc (t - 1) b ⊆ Iic 0 from fun _ hs => hs.2.trans hb)
    ordConnected_Icc ⟨t - 1, ⟨le_rfl, hab.le⟩, b, ⟨hab.le, le_rfl⟩, hab.ne⟩
  have hsec : ∀ s ∈ Icc (t - 1) b, (F.connection s).NonnegativeSectionalCurvature := by
    intro s hs q a c
    exact (K.flow.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      q (K.nonnegative_curvature_operator s (hs.2.trans hb) q) a c
  symm
  apply Submodule.eq_of_le_of_finrank_eq
    (ricciKernel_antitoneOn ricciFlowCurvatureTheory hab F hsec y
      ⟨by linarith, ht⟩ ⟨hab.le, le_rfl⟩ ht)
  change ricciNullity (K.flow.connection b) y = ricciNullity (K.flow.connection t) y
  rw [K.ricciNullity_eq_one_on_past_of_null_plane hb x v w hv hw hvw hzero b le_rfl y,
    K.ricciNullity_eq_one_on_past_of_null_plane hb x v w hv hw hvw hzero t ht y]



theorem inner_eq_on_past_of_null_plane
    (t : ℝ) (ht : t ≤ b) (y : M) (z u : TangentSpace (𝓡 3) y)
    (hz : z ∈ ricciKernel (K.flow.connection b) y) :
    (K.flow.metric t).inner y z u = (K.flow.metric b).inner y z u := by
  let q : ℝ → ℝ := fun s => (K.flow.metric s).inner y z u
  have hab : t - 1 < b := by linarith
  have hd (s : ℝ) (hs : s ∈ Icc (t - 1) b) :
      HasDerivWithinAt q 0 (Icc (t - 1) b) s := by
    have hn : (K.flow.connection s).ricci y z u = 0 := by
      apply (mem_ricciKernel _ _ _).mp _ u
      rw [K.ricciKernel_eq_on_past_of_null_plane hb x v w hv hw hvw hzero s hs.2 y]
      exact hz
    simpa only [q, hn, mul_zero] using
      (K.flow.equation s (hs.2.trans hb) y z u).mono
        (show Icc (t - 1) b ⊆ Iic 0 from fun _ hr => hr.2.trans hb)
  have hdiff : DifferentiableOn ℝ q (Icc (t - 1) b) :=
    fun s hs => (hd s hs).differentiableWithinAt
  have hderiv (s : ℝ) (hs : s ∈ Ico (t - 1) b) :
      derivWithin q (Icc (t - 1) b) s = 0 :=
    (hd s ⟨hs.1, hs.2.le⟩).derivWithin
      (uniqueDiffOn_Icc hab s ⟨hs.1, hs.2.le⟩)
  exact (constant_of_derivWithin_zero hdiff hderiv t ⟨by linarith, ht⟩).trans
    (constant_of_derivWithin_zero hdiff hderiv b ⟨hab.le, le_rfl⟩).symm



theorem exists_fixed_local_parallel_unit_null_section
    (y : M) :
    ∃ (U : Set M) (V : (q : M) → TangentSpace (𝓡 3) q),
      IsOpen U ∧ y ∈ U ∧
      ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) U ∧
      ∀ t ≤ b, ∀ q ∈ U,
        (K.flow.metric t).inner q (V q) (V q) = 1 ∧
        (∀ z, (K.flow.connection t).ricci q (V q) z = 0) ∧
        ∀ z, (K.flow.connection t).connection V q z = 0 := by
  have hslab (t : ℝ) (ht : t ≤ b) :
      Icc (t - 1) t ⊆ Iic (0 : ℝ) := fun _ hs => (hs.2.trans ht).trans hb
  let F (t : ℝ) (ht : t ≤ b) := restrictFlow K.flow (hslab t ht) ordConnected_Icc
    ⟨t - 1, ⟨le_rfl, by linarith⟩, t, ⟨by linarith, le_rfl⟩, by linarith⟩
  have hsec (t : ℝ) (ht : t ≤ b) :
      ∀ s ∈ Icc (t - 1) t, ((F t ht).connection s).NonnegativeSectionalCurvature := by
    intro s hs q a c
    exact (K.flow.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      q (K.nonnegative_curvature_operator s (hslab t ht hs) q) a c
  obtain ⟨U, V, hU, hy, hV, hn⟩ := exists_local_parallel_unit_ricci_null_section
    ricciFlowCurvatureTheory (by linarith : b - 1 < b) (F b le_rfl) (hsec b le_rfl)
    (K.ricciNullity_eq_one_on_past_of_null_plane hb x v w hv hw hvw hzero b le_rfl) y
  have hnull (t : ℝ) (ht : t ≤ b) (q : M) (hq : q ∈ U) :
      V q ∈ ricciKernel (K.flow.connection t) q := by
    rw [K.ricciKernel_eq_on_past_of_null_plane hb x v w hv hw hvw hzero t ht q]
    exact (mem_ricciKernel _ _ _).mpr (hn q hq).2.1
  have hunit (t : ℝ) (ht : t ≤ b) (q : M) (hq : q ∈ U) :
      (K.flow.metric t).inner q (V q) (V q) = 1 := by
    rw [K.inner_eq_on_past_of_null_plane hb x v w hv hw hvw hzero t ht q (V q) (V q)
      (hnull b le_rfl q hq)]
    exact (hn q hq).1
  refine ⟨U, V, hU, hy, hV, fun t ht q hq => ⟨hunit t ht q hq,
    (mem_ricciKernel _ _ _).mp (hnull t ht q hq), ?_⟩⟩
  intro z
  exact connection_eq_zero_of_terminal_unit_null ricciFlowCurvatureTheory
    (by linarith : t - 1 < t) (F t ht) (hsec t ht) V
    (hV.contMDiffAt (hU.mem_nhds hq))
    (Filter.Eventually.mono (hU.mem_nhds hq)
      fun p hp => (mem_ricciKernel _ _ _).mp (hnull t ht p hp))
    (Filter.Eventually.mono (hU.mem_nhds hq) fun p hp => hunit t ht p hp)
    (K.ricciNullity_eq_one_on_past_of_null_plane hb x v w hv hw hvw hzero t ht q) z



theorem nullOrientationCover_of_null_plane :
    Nonempty (NullOrientationCover (K.flow.connection b)) := by
  have hab : b - 1 < b := by linarith
  let F := restrictFlow K.flow
    (show Icc (b - 1) b ⊆ Iic 0 from fun _ hs => hs.2.trans hb)
    ordConnected_Icc ⟨b - 1, ⟨le_rfl, hab.le⟩, b, ⟨hab.le, le_rfl⟩, hab.ne⟩
  have hsec : ∀ s ∈ Icc (b - 1) b, (F.connection s).NonnegativeSectionalCurvature := by
    intro s hs q a c
    exact (K.flow.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      q (K.nonnegative_curvature_operator s (hs.2.trans hb) q) a c
  have hdim := K.ricciNullity_eq_one_on_past_of_null_plane hb x v w hv hw hvw hzero b le_rfl
  exact ⟨{
    covering := unitRicciKernel_isCoveringMap_of_terminal_nullity_one
      ricciFlowCurvatureTheory hab F hsec hdim
    fiber_card := unitRicciKernel_fiber_card_of_terminal_nullity_one
      ricciFlowCurvatureTheory hab F hsec hdim
    deck := unitRicciKernelDeckHomeomorph (K.flow.connection b)
    deck_involutive := unitRicciKernelReverse_involutive (K.flow.connection b)
    deck_projection := unitRicciKernelProjection_reverse (K.flow.connection b)
    deck_free := unitRicciKernelReverse_fixedPointFree (K.flow.connection b) }⟩

end PoincareConjecture.AncientKappaSolution
