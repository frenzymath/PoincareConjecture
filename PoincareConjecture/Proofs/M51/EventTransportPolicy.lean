import PoincareConjecture.Proofs.M51.EventTransport
import PoincareConjecture.Proofs.M51.EventTransportMetricCovariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SurgeryEventData

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

@[simp] theorem transport_tMinus : (E').tMinus = E.tMinus := rfl

@[simp] theorem transport_terminal : (E').terminal = E.terminal := rfl

@[simp] theorem transport_limit_metric : (E').limit_metric = E.limit_metric := rfl

@[simp] theorem transport_limit_connection :
    (E').limit_connection = E.limit_connection := rfl

@[simp] theorem transport_cap_count : (E').cap_count = E.cap_count := rfl

@[simp] theorem transport_necks : (E').necks = E.necks := rfl

@[simp] theorem transport_local_result : (E').local_result = E.local_result := rfl

@[simp] theorem transport_disappearing_start :
    (E').disappearing_start = E.disappearing_start := rfl

@[simp] theorem transport_pre_flow :
    (E').pre_flow = E.pre_flow.pullbackDiffeomorph (p).symm := rfl

@[simp] theorem transport_pre_identify (t : Set.Ico E.tMinus T)
    (x : (slice' E.tMinus).carrier) :
    (E').pre_identify t x = φ t (E.pre_identify t ((p).symm x)) := rfl

@[simp] theorem transport_limit_identify_map (x : (slice' E.tMinus).carrier) :
    (E').limit_identify.map x = E.limit_identify.map ((p).symm x) := rfl

@[simp] theorem transport_limit_identify_inverse (x : E.terminal.carrier) :
    (E').limit_identify.inverse x = p (E.limit_identify.inverse x) := rfl

@[simp] theorem transport_retention_map (x : (slice' E.tMinus).carrier) :
    (E').retention.map x = ψ (E.retention.map ((p).symm x)) := rfl

@[simp] theorem transport_retention_inverse (x : (slice' T).carrier) :
    (E').retention.inverse x = p (E.retention.inverse (ψ.symm x)) := rfl

@[simp] theorem transport_local_embed (i : Fin E.cap_count)
    (x : (E.local_result i).output.carrier) :
    (E').local_embed i x = ψ (E.local_embed i x) := rfl

theorem transport_regular_limit : (E').regular_limit = p '' E.regular_limit :=
  ((p).image_eq_preimage_symm _).symm

theorem transport_retained_pre : (E').retained_pre = p '' E.retained_pre :=
  ((p).image_eq_preimage_symm _).symm

theorem transport_retained_post : (E').retained_post = ψ '' E.retained_post :=
  (ψ.image_eq_preimage_symm _).symm

theorem transport_retained_image :
    (E').limit_identify.map '' (E').retained_pre =
      E.limit_identify.map '' E.retained_pre :=
  M51EventTransport.limit_identify_image_preimage E p E.retained_pre

theorem transport_preservation : M33NonemptyEventDataPreservation E E' where
  terminal_eq := rfl
  limit_metric_heq := HEq.rfl
  limit_connection_heq := HEq.rfl
  cap_count_eq := rfl
  necks_heq := HEq.rfl
  retained_image_heq := heq_of_eq (E.transport_retained_image φ ψ hφ hψ D)

theorem transport_policy (hE : Nonempty (SurgeryEventTerminalPolicy E)) :
    Nonempty (SurgeryEventTerminalPolicy E') :=
  (E.transport_preservation φ ψ hφ hψ D).transportPolicy rfl hE

end PoincareConjecture.SurgeryEventData
