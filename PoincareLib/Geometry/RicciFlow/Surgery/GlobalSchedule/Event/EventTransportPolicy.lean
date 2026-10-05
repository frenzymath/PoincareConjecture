import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Event.EventTransport
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Event.EventTransportMetricCovariance

/-!
# Literal terminal data and policy after event transport

The event transport fixes the terminal geometry, and its new retained region
has exactly the old terminal image.  These are precisely the M33 data needed
to retain the source terminal policy.
The source is Morgan--Tian Definition 15.8, pp. 361-362, as used by the
global construction in Section 17.2, pp. 409-411.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice slice' : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier}
    {metric' : ∀ t, RiemannianMetric 3 (slice' t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T)
    (φ : ∀ t : Set.Ico E.tMinus T,
      Diffeomorph (𝓡 3) (𝓡 3) (slice t.1).carrier (slice' t.1).carrier ∞)
    (ψ : Diffeomorph (𝓡 3) (𝓡 3) (slice T).carrier (slice' T).carrier ∞)
    (hφ : ∀ (t : Set.Ico E.tMinus T) (x : (slice t.1).carrier) v w,
      (metric' t.1).inner (φ t x)
        (mfderiv (𝓡 3) (𝓡 3) (φ t) x v)
        (mfderiv (𝓡 3) (𝓡 3) (φ t) x w) =
        (metric t.1).inner x v w)
    (hψ : ∀ (x : (slice T).carrier) v w,
      (metric' T).inner (ψ x)
        (mfderiv (𝓡 3) (𝓡 3) ψ x v)
        (mfderiv (𝓡 3) (𝓡 3) ψ x w) =
        (metric T).inner x v w)
    (D : M51EventTransport.MetricLimitTransportData E
      (φ ⟨E.tMinus, ⟨le_rfl, E.tMinus_lt⟩⟩))

local notation "E'" => E.transport φ ψ hφ hψ D
local notation "p" => φ (Subtype.mk E.tMinus (And.intro le_rfl E.tMinus_lt))

/-- Transport keeps the reference time; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_tMinus : (E').tMinus = E.tMinus := rfl

/-- Transport keeps the terminal carrier; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_terminal : (E').terminal = E.terminal := rfl

/-- Transport keeps the terminal metric; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_limit_metric : (E').limit_metric = E.limit_metric := rfl

/-- Transport keeps the terminal connection; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_limit_connection :
    (E').limit_connection = E.limit_connection := rfl

/-- Transport keeps the number of caps; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_cap_count : (E').cap_count = E.cap_count := rfl

/-- Transport keeps the complete neck family; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_necks : (E').necks = E.necks := rfl

/-- Transport keeps the local surgery results; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_local_result : (E').local_result = E.local_result := rfl

/-- Transport keeps the disappearing interval; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_disappearing_start :
    (E').disappearing_start = E.disappearing_start := rfl

/-- The pre-flow is the fixed reference pullback; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_pre_flow :
    (E').pre_flow = E.pre_flow.pullbackDiffeomorph (p).symm := rfl

/-- Pre-identifications conjugate the source maps; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_pre_identify (t : Set.Ico E.tMinus T)
    (x : (slice' E.tMinus).carrier) :
    (E').pre_identify t x = φ t (E.pre_identify t ((p).symm x)) := rfl

/-- The limit map precomposes by the inverse reference map; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_limit_identify_map (x : (slice' E.tMinus).carrier) :
    (E').limit_identify.map x = E.limit_identify.map ((p).symm x) := rfl

/-- The inverse limit map postcomposes by the reference map; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_limit_identify_inverse (x : E.terminal.carrier) :
    (E').limit_identify.inverse x = p (E.limit_identify.inverse x) := rfl

/-- The retention map is conjugated on both carriers; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_retention_map (x : (slice' E.tMinus).carrier) :
    (E').retention.map x = ψ (E.retention.map ((p).symm x)) := rfl

/-- The inverse retention map uses the inverse conjugate; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_retention_inverse (x : (slice' T).carrier) :
    (E').retention.inverse x = p (E.retention.inverse (ψ.symm x)) := rfl

/-- The local embedding is postcomposed on the target; Definition 15.8, pp. 361-362. -/
@[simp] theorem transport_local_embed (i : Fin E.cap_count)
    (x : (E.local_result i).output.carrier) :
    (E').local_embed i x = ψ (E.local_embed i x) := rfl

/-- The regular limit domain is the source image; Definition 15.8, pp. 361-362. -/
theorem transport_regular_limit : (E').regular_limit = p '' E.regular_limit :=
  ((p).image_eq_preimage_symm _).symm

/-- The retained pre-region is the source image; Definition 15.8, pp. 361-362. -/
theorem transport_retained_pre : (E').retained_pre = p '' E.retained_pre :=
  ((p).image_eq_preimage_symm _).symm

/-- The retained post-region is the source image; Definition 15.8, pp. 361-362. -/
theorem transport_retained_post : (E').retained_post = ψ '' E.retained_post :=
  (ψ.image_eq_preimage_symm _).symm

/-- The terminal image of the retained region is unchanged; Definition 15.8, pp. 361-362. -/
theorem transport_retained_image :
    (E').limit_identify.map '' (E').retained_pre =
      E.limit_identify.map '' E.retained_pre :=
  M51EventTransport.limit_identify_image_preimage E p E.retained_pre

/-- Event transport supplies M33's literal terminal-data witness;
Definition 15.8, pp. 361-362. -/
theorem transport_preservation : M33NonemptyEventDataPreservation E E' where
  terminal_eq := rfl
  limit_metric_heq := HEq.rfl
  limit_connection_heq := HEq.rfl
  cap_count_eq := rfl
  necks_heq := HEq.rfl
  retained_image_heq := heq_of_eq (E.transport_retained_image φ ψ hφ hψ D)

/-- Reuse the cuts and terminal core of the source event;
Definition 15.8, pp. 361-362. -/
theorem transport_policy (hE : Nonempty (SurgeryEventTerminalPolicy E)) :
    Nonempty (SurgeryEventTerminalPolicy E') :=
  (E.transport_preservation φ ψ hφ hψ D).transportPolicy rfl hE

end PoincareMT.SurgeryEventData
