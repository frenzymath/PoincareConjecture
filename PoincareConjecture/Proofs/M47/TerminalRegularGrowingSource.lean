import PoincareConjecture.Proofs.M47.TerminalRegularStageFamily
import PoincareConjecture.Proofs.M47.TerminalRegularAtlasCapture
import PoincareConjecture.Proofs.M47.TerminalRegularComponentInverse
import PoincareConjecture.Proofs.M47.TerminalRegularAtlasInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem component_chart
    {S : RepairedControlledSchedulesData.{u}}
    {B : M47ComponentAnalyticBounds.{u} S.setup.C} {p : SurgeryParameterPrefix S.constants}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {W : M33RegularHistoryWindow F}
    {H : M33RegularHistoryData W} {base Q r A tau0 tau K L a R rho : ℝ} {N : ℕ}
    {center : (F.slice base).carrier}
    (data : TerminalRegularStageData S B p O H base Q r A tau0 tau K L a R rho N center)
    (htau : 0 < tau) :
    let U := terminalRegularStageSource F base Q A center
    let h : RiemannianMetric 3 (F.slice base).carrier :=
      M13.scaleSmoothMetric (F.metric base) Q data.original.scale_pos
    let C := Poincare.connectedComponentOpens E center
    letI := terminalSourceComponentMetricSpace h center
    ∃ j : PartialDiffeomorph (𝓡 3) (𝓡 3) U C ∞,
      j.source = univ ∧ j.target = Metric.ball ⟨center, mem_connectedComponent⟩ A ∧
      (∀ z : U, (j z).val = z.val) ∧ j data.point = ⟨center, mem_connectedComponent⟩ ∧
      ∀ z (v w : TangentSpace (𝓡 3) z),
        (data.flow.metric 0).inner z v w = (h.connectedComponentMetric center).inner (j z)
          (mfderiv (𝓡 3) (𝓡 3) j z v) (mfderiv (𝓡 3) (𝓡 3) j z w) := by
  let U := terminalRegularStageSource F base Q A center
  let h0 : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau.le, le_rfl⟩
  let e := terminalSourceNormal_historyCylinder H U data.time data.cylinder
  have he := terminalSourceNormal_historyCylinder_maps H U data.time data.cylinder
  have hm (z : U) (v w : TangentSpace (𝓡 3) z) :
      (data.flow.metric 0).inner z v w = e.pullbackInner 0 h0 z.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice base).carrier) z v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice base).carrier) z w) :=
    (data.metric 0 h0 z v w).trans (he.2 0 h0 z.val z.property _ _).symm
  have hn (z : U) : (data.flow.connection 0).curvatureTensorNorm z =
      (F.connection (base + 0 / Q)).curvatureTensorNorm (e.forward 0 h0 z.val) / Q := by
    rw [congrFun (he.1 0 h0) z, H.curvature_norm_pullback]
    exact data.norm 0 h0 z
  exact terminalSource_regular_component_inverse center data.point data.point_eq e h0
    (data.flow.metric 0) (data.terminal h0).2.2
    (terminalSourceNormal_terminal_readouts U data.point e h0 data.flow hm hn).1

section Family

variable (S : RepairedControlledSchedulesData.{u})
  (B : M47ComponentAnalyticBounds.{u} S.setup.C) (p : SurgeryParameterPrefix S.constants)
  (F : ℕ → SurgeryFlowData.{u}) (O : ∀ k, SurgeryObservation (F k))
  (W : ∀ k, M33RegularHistoryWindow (F k)) (H : ∀ k, M33RegularHistoryData (W k))
  (base Q r A tau0 tau K L R rho : ℕ → ℝ) (N : ℕ → ℕ)
  (center : ∀ k, ((F k).slice (base k)).carrier)
  (data : ∀ k j, j ≤ k → TerminalRegularStageData S B p (O k) (H k)
    (base k) (Q k) (r k) (A j) (tau0 j) (tau j) (K j) (L j)
    ((j : ℝ) + 1) (R j) (rho j) (N j) (center k))

local notation "M" => (fun k : ℕ => Poincare.connectedComponentOpens E (center k))
local notation "gPhysical" => (fun k : ℕ =>
  M13.scaleSmoothMetric (SurgeryFlowData.metric (F k) (base k)) (Q k)
    (SurgeryFlowCylinder.scale_pos (TerminalRegularStageData.original (data k 0 (Nat.zero_le k)))))
local notation "g" => (fun k : ℕ =>
  RiemannianMetric.connectedComponentMetric (gPhysical k) (center k))
local notation "point" => (fun k : ℕ => (Subtype.mk (center k) mem_connectedComponent : M k))

variable {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (𝓡 3) ∞ X] [T3Space X]
  (nu : ℕ → ℕ) (V : ℕ → Set X) (pX : X)
  (f : ∀ k : ℕ, X → Poincare.connectedComponentOpens E (center (nu k)))

theorem terminalSource_regular_growing_sources
    (hnu : StrictMono nu) (htau : ∀ j, 0 < tau j)
    (hA : ∀ s : ℝ, 0 < s → ∃ j, s ≤ A j)
    (hV : ∀ k, IsOpen (V k)) (hmono : Monotone V)
    (hcompact : ∀ j, IsCompact (closure (V j))) (hpX : ∀ j, pX ∈ V j)
    (hgeometry : ∀ k, Topology.IsOpenEmbedding (fun x : V k => f k x) ∧
      IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (f k) (V k))
    (hbase : ∀ k, f k pX = point (nu k))
    (c : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (e : ∀ k, ℕ → E → M (nu k)) (bound : ℕ → ℝ)
    (hbound : letI : ∀ k, MetricSpace (M k) :=
        fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
      ∀ k i z, z ∈ (c i).target → dist (point (nu k)) (e k i z) ≤ bound i)
    (happrox : letI : ∀ k, MetricSpace (M k) :=
        fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
      ∀ i C, IsCompact C → C ⊆ (c i).target → TendstoUniformlyOn
        (fun k z => dist (f k ((c i).symm z)) (e k i z)) (fun _ => 0) atTop C) :
    ∃ J lambda : ℕ → ℕ, StrictMono lambda ∧
      ∃ available : ∀ k : ℕ, J k ≤ nu (lambda k),
      ∃ j : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3)
          (terminalRegularStageSource (F (nu (lambda k))) (base (nu (lambda k)))
            (Q (nu (lambda k))) (A (J k)) (center (nu (lambda k)))) (M (nu (lambda k))) ∞,
        (∀ k, (j k).source = univ) ∧
        (∀ k, (j k).target = (g (nu (lambda k))).ball (point (nu (lambda k))) (A (J k))) ∧
        (∀ k z, (j k z).val = z.val) ∧
        (∀ k, j k (data (nu (lambda k)) (J k) (available k)).point = point (nu (lambda k))) ∧
        (∀ k z (v w : TangentSpace (𝓡 3) z),
          ((data (nu (lambda k)) (J k) (available k)).flow.metric 0).inner z v w =
            (g (nu (lambda k))).inner (j k z)
            (mfderiv (𝓡 3) (𝓡 3) (j k) z v) (mfderiv (𝓡 3) (𝓡 3) (j k) z w)) ∧
        ∃ phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X
            (terminalRegularStageSource (F (nu (lambda k))) (base (nu (lambda k)))
              (Q (nu (lambda k))) (A (J k)) (center (nu (lambda k)))) ∞,
          (∀ k, (phi k : X → _) = (j k).symm ∘ f (lambda k)) ∧
          (∀ k, (phi k).source = V k) ∧
          (∀ (k : ℕ) (x : X), x ∈ V k → j k (phi k x) = f (lambda k) x) ∧
          ∀ k, phi k pX = (data (nu (lambda k)) (J k) (available k)).point := by
  classical
  let : ∀ k, MetricSpace (M k) :=
    fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
  let : Nonempty X := ⟨pX⟩
  choose radius hradius hcapture using fun j =>
    terminalSource_compact_atlas_image_radius c hcoverC (fun k => M (nu k))
      (fun k => point (nu k)) f e bound hbound happrox (hcompact j)
  choose J hJ using fun j => hA (radius j + 1) (by linarith [hradius j])
  have hstage (j : ℕ) : ∀ᶠ k in atTop,
      J j ≤ nu k ∧ MapsTo (f k) (closure (V j))
        (Metric.ball (point (nu k)) (A (J j))) := by
    filter_upwards [hnu.tendsto_atTop.eventually (eventually_ge_atTop (J j)), hcapture j]
      with k hk hc
    refine ⟨hk, fun x hx => ?_⟩
    exact Metric.ball_subset_ball (by linarith [hJ j]) (hc hx)
  obtain ⟨lambda, hlambda, hselected⟩ :=
    Poincare.exists_strictMono_forall_le_of_eventually hstage
  let available := fun k => (hselected k k le_rfl).1
  let selected := fun k => data (nu (lambda k)) (J k) (available k)
  choose j hsource htarget hprojection hpoint hmetric using
    fun k => component_chart (selected k) (htau (J k))
  have htarget' (k : ℕ) : (j k).target =
      (g (nu (lambda k))).ball (point (nu (lambda k))) (A (J k)) :=
    (htarget k).trans (terminalSourceComponent_balls (gPhysical (nu (lambda k)))
      (center (nu (lambda k))) (point (nu (lambda k))) (A (J k))).1
  have hinverse (k : ℕ) :
      ∃ phi : PartialDiffeomorph (𝓡 3) (𝓡 3) X
          (terminalRegularStageSource (F (nu (lambda k))) (base (nu (lambda k)))
            (Q (nu (lambda k))) (A (J k)) (center (nu (lambda k)))) ∞,
        (phi : X → _) = (j k).symm ∘ f (lambda k) ∧ phi.source = V k ∧
        (∀ x ∈ V k, j k (phi x) = f (lambda k) x) ∧ phi pX = (selected k).point := by
    have hsubset : V k ⊆ V (lambda k) := hmono (hlambda.id_le k)
    have hembed : Topology.IsOpenEmbedding (fun x : V k => f (lambda k) x) :=
      (hgeometry (lambda k)).1.comp
        (Topology.IsOpenEmbedding.inclusion hsubset ((hV k).preimage continuous_subtype_val))
    have hcap : MapsTo (f (lambda k)) (V k) (j k).target := by
      rw [htarget k]
      exact fun x hx => (hselected k k le_rfl).2 (subset_closure hx)
    obtain ⟨phi, hphi, hdom, hfactor, hbased⟩ := terminalSource_atlas_actual_inverse
      (j k) (hsource k) (hV k) (f (lambda k)) hembed
      (fun x => (hgeometry (lambda k)).2 ⟨x.val, hsubset x.property⟩) hcap
    exact ⟨phi, hphi, hdom, hfactor,
      hbased pX (hpX k) (selected k).point ((hbase (lambda k)).trans (hpoint k).symm)⟩
  choose phi hphi hdom hfactor hbased using hinverse
  exact ⟨J, lambda, hlambda, available, j, hsource, htarget', hprojection, hpoint, hmetric,
    phi, hphi, hdom, hfactor, hbased⟩

end Family

end PoincareConjecture.M47
