import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.NonlinearLp









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff SchwartzMap LineDeriv Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => EuclideanSpace ℝ (Fin m)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem supported_graph_limit (K : Set V) (f : ℕ → supportedTests K)
    (hf : CauchySeq (fun k => (f k : 𝓢(V, ℝ)).toLp 2 volume))
    (hd : ∀ j : Fin n, CauchySeq (fun k =>
      (∂_{EuclideanSpace.single j (1 : ℝ)} (f k : 𝓢(V, ℝ))).toLp 2 volume)) :
    ∃ u : dirichletForm K, Tendsto (fun k => intoDirichletForm K (f k)) atTop (𝓝 u) := by
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hf
  choose d hdlim using fun j => cauchySeq_tendsto_of_complete (hd j)
  have hvK : v ∈ dirichletValue K :=
    (testValue K).range.isClosed_topologicalClosure.mem_of_tendsto hv
      (Eventually.of_forall fun k =>
        (testValue K).range.le_topologicalClosure (LinearMap.mem_range_self _ (f k)))
  have hvs : Tendsto (fun k => intoDirichletValue K (f k)) atTop
      (𝓝 (⟨v, hvK⟩ : dirichletValue K)) := tendsto_subtype_rng.mpr hv
  have hds : Tendsto (fun k => testGradient K (f k)) atTop (𝓝 (WithLp.toLp 2 d)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin n => L2)).continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr hdlim)
  let w : DirichletAmbient K := WithLp.toLp 2 ((⟨v, hvK⟩ : dirichletValue K), WithLp.toLp 2 d)
  have hwlim : Tendsto (fun k => dirichletImage K (f k)) atTop (𝓝 w) :=
    (WithLp.prod_continuous_toLp 2 (dirichletValue K)
      (DirichletGradient n)).continuousAt.tendsto.comp
      (hvs.prodMk_nhds hds)
  have hw : w ∈ dirichletForm K :=
    (dirichletImage K).range.isClosed_topologicalClosure.mem_of_tendsto hwlim
      (Eventually.of_forall fun k =>
        (dirichletImage K).range.le_topologicalClosure (LinearMap.mem_range_self _ (f k)))
  exact ⟨⟨w, hw⟩, tendsto_subtype_rng.mpr hwlim⟩

theorem vectorTestForm_denseRange (K : Set V) : DenseRange (vectorTestForm (m := m) K) := by
  have hd : DenseRange (Pi.map (fun _ : Fin m => intoDirichletForm K)) :=
    DenseRange.piMap fun _ => intoDirichletForm_denseRange K
  exact ((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin m => dirichletForm K)).symm.surjective.denseRange).comp hd
      (PiLp.continuous_toLp 2 (fun _ : Fin m => dirichletForm K))

def nonlinearSupportedTest {K : Set V} (hK : IsCompact K)
    (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T) (hT0 : ∀ x, T (x, 0) = 0)
    (f : Fin m → supportedTests K) : supportedTests K :=
  ⟨nonlinearTestSchwartz T hT hT0 (schwartzField (fun i => (f i : 𝓢(V, ℝ))))
    (schwartzField_hasCompactSupport hK f), by
      intro x hx
      change T (x, schwartzField (fun i => (f i : 𝓢(V, ℝ))) x) = 0
      have hz : schwartzField (fun i => (f i : 𝓢(V, ℝ))) x = 0 := by
        rw [schwartzField_apply]
        apply PiLp.ext
        intro i
        exact (f i).property x hx
      rw [hz, hT0]⟩

private theorem nonlinear_test_value_limit {K : Set V} (hK : IsCompact K)
    (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T) (hT0 : ∀ x, T (x, 0) = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ x z w, ‖T (x, z) - T (x, w)‖ ≤ C * ‖z - w‖)
    (u : PiLp 2 (fun _ : Fin m => dirichletForm K))
    (f : ℕ → Fin m → supportedTests K)
    (hv : Tendsto (fun k => (schwartzField (fun i => (f k i : 𝓢(V, ℝ)))).toLp 2 volume)
      atTop (𝓝 (dirichletFieldValue K u)))
    (v : dirichletForm K)
    (hvlim : Tendsto (fun k => intoDirichletForm K (nonlinearSupportedTest hK T hT hT0 (f k)))
      atTop (𝓝 v)) :
    (dirichletInclusion K v : L2) =
      nonlinearFieldLp T hT.continuous hT0 hLip (dirichletFieldValue K u) := by
  have h₁ : Tendsto (fun k =>
      (nonlinearSupportedTest hK T hT hT0 (f k) : 𝓢(V, ℝ)).toLp 2 volume)
      atTop (𝓝 (dirichletInclusion K v : L2)) :=
    (((dirichletValue K).subtypeL.comp (dirichletInclusion K)).continuous.tendsto v).comp hvlim
  have h₂ := ((nonlinearFieldLp_continuous T hT.continuous hT0 hC hLip).tendsto
    (dirichletFieldValue K u)).comp hv
  have h₃ : Tendsto (fun k =>
      (nonlinearSupportedTest hK T hT hT0 (f k) : 𝓢(V, ℝ)).toLp 2 volume)
      atTop (𝓝 (nonlinearFieldLp T hT.continuous hT0 hLip (dirichletFieldValue K u))) := by
    apply h₂.congr'
    apply Eventually.of_forall
    intro k
    exact nonlinearFieldLp_schwartz T hT hT0 hLip _ (schwartzField_hasCompactSupport hK (f k))
  exact tendsto_nhds_unique h₁ h₃

theorem nonlinearSupportedTest_graph_limit {K : Set V} (hK : IsCompact K)
    (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T) (hT0 : ∀ x, T (x, 0) = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ x z w, ‖T (x, z) - T (x, w)‖ ≤ C * ‖z - w‖)
    (hspace : ∀ j : Fin n, ∀ x z w,
      ‖nonlinearSpaceJet T x z (EuclideanSpace.single j (1 : ℝ)) -
        nonlinearSpaceJet T x w (EuclideanSpace.single j (1 : ℝ))‖ ≤ C * ‖z - w‖)
    (hval : ∀ x z, ‖nonlinearValueJet T x z‖ ≤ C)
    (hvalLip : ∀ x z w, ‖nonlinearValueJet T x z - nonlinearValueJet T x w‖ ≤ C * ‖z - w‖)
    (u : PiLp 2 (fun _ : Fin m => dirichletForm K))
    (f : ℕ → Fin m → supportedTests K)
    (hflim : Tendsto (fun k => vectorTestForm K (f k)) atTop (𝓝 u)) :
    ∃ v : dirichletForm K,
      Tendsto (fun k => intoDirichletForm K (nonlinearSupportedTest hK T hT hT0 (f k)))
        atTop (𝓝 v) ∧
      (dirichletInclusion K v : L2) =
        nonlinearFieldLp T hT.continuous hT0 hLip (dirichletFieldValue K u) := by
  let X (k : ℕ) : 𝓢(V, Z) := schwartzField (fun i => (f k i : 𝓢(V, ℝ)))
  have hc (k : ℕ) : HasCompactSupport (X k) := schwartzField_hasCompactSupport hK (f k)
  have hv : Tendsto (fun k => (X k).toLp 2 volume) atTop (𝓝 (dirichletFieldValue K u)) := by
    simpa only [Function.comp_def, dirichletFieldValue_test, X] using
      ((dirichletFieldValue K).continuous.tendsto u).comp hflim
  have hd (j : Fin n) : CauchySeq (fun k =>
      (∂_{EuclideanSpace.single j (1 : ℝ)} (X k)).toLp 2 volume) := by
    have hl := ((dirichletFieldPartial K j).continuous.tendsto u).comp hflim
    simpa only [Function.comp_def, dirichletFieldPartial_test, X] using hl.cauchySeq
  obtain ⟨v, hvlim⟩ : ∃ v : dirichletForm K,
      Tendsto (fun k => intoDirichletForm K (nonlinearSupportedTest hK T hT hT0 (f k)))
        atTop (𝓝 v) := supported_graph_limit K
    (fun k => nonlinearSupportedTest hK T hT hT0 (f k))
    (nonlinearTestSchwartz_value_cauchy T hT hT0 X hc hC hLip hv.cauchySeq)
    (fun j => nonlinearTestSchwartz_partial_cauchy T hT hT0 X hc
      (EuclideanSpace.single j (1 : ℝ)) hC (hspace j) hval hvalLip hv.cauchySeq (hd j))
  exact ⟨v, hvlim, nonlinear_test_value_limit hK T hT hT0 hC hLip u f hv v hvlim⟩



theorem exists_nonlinear_dirichlet_test {K : Set V} (hK : IsCompact K)
    (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T) (hT0 : ∀ x, T (x, 0) = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ x z w, ‖T (x, z) - T (x, w)‖ ≤ C * ‖z - w‖)
    (hspace : ∀ j : Fin n, ∀ x z w,
      ‖nonlinearSpaceJet T x z (EuclideanSpace.single j (1 : ℝ)) -
        nonlinearSpaceJet T x w (EuclideanSpace.single j (1 : ℝ))‖ ≤ C * ‖z - w‖)
    (hval : ∀ x z, ‖nonlinearValueJet T x z‖ ≤ C)
    (hvalLip : ∀ x z w, ‖nonlinearValueJet T x z - nonlinearValueJet T x w‖ ≤ C * ‖z - w‖)
    (u : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    ∃ f : ℕ → Fin m → supportedTests K, ∃ v : dirichletForm K,
      Tendsto (fun k => vectorTestForm K (f k)) atTop (𝓝 u) ∧
      Tendsto (fun k => intoDirichletForm K (nonlinearSupportedTest hK T hT hT0 (f k)))
        atTop (𝓝 v) ∧
      (dirichletInclusion K v : L2) =
        nonlinearFieldLp T hT.continuous hT0 hLip (dirichletFieldValue K u) := by
  have hu : u ∈ closure (Set.range (vectorTestForm (m := m) K)) := vectorTestForm_denseRange K u
  obtain ⟨s, hs, hslim⟩ := mem_closure_iff_seq_limit.mp hu
  choose f hf using hs
  have hflim : Tendsto (fun k => vectorTestForm K (f k)) atTop (𝓝 u) :=
    hslim.congr' (Eventually.of_forall fun k => (hf k).symm)
  refine (nonlinearSupportedTest_graph_limit
    hK T hT hT0 hC hLip hspace hval hvalLip u f hflim).elim ?_
  intro v hv
  exact ⟨f, v, hflim, hv.1, hv.2⟩

end PoincareConjecture.M35.Uniqueness.Heat
