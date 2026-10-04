import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Restricting slabs and assembling the infinite horizon

The continuation following Claim 11.35, printed p. 291, requires slabs
of arbitrarily large finite duration. Cofinal durations on the original
sequence supply exactly the frozen M30 long-control field.
Derivation: `claim11_35-finite-slabs.md`. The actual stage construction
remains an explicit hypothesis; these constructors do not extend a slab.
-/

set_option autoImplicit false

open scoped ENNReal Topology

universe u

namespace PoincareMT.M32

/-- Restrict a compatible cylinder without changing its clock or points;
the continuation after Claim 11.35, printed p. 291, uses shorter slabs. -/
noncomputable def restrictCylinderTime
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I J : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U) (hJI : J ⊆ I) :
    GeneralizedFlowCylinder F C origin scale J U where
  scale_pos := e.scale_pos
  forward s hs := e.forward s (hJI hs)
  inverse s hs := e.inverse s (hJI hs)
  forward_smooth s hs := e.forward_smooth s (hJI hs)
  inverse_smooth s hs := e.inverse_smooth s (hJI hs)
  left_inverse s hs := e.left_inverse s (hJI hs)
  right_inverse s hs := e.right_inverse s (hJI hs)
  embedding := e.embedding.comp
    ((Topology.IsEmbedding.inclusion hJI).prodMap Topology.IsEmbedding.id)
  vertical_compatibility s hs x hx := by
    obtain ⟨b, y, delta, hdelta, hlocal⟩ := e.vertical_compatibility s (hJI hs) x hx
    exact ⟨b, y, delta, hdelta, fun s' hs' hdist => hlocal s' (hJI hs') hdist⟩

/-- A longer actual slab restricts to a shorter half-open time interval,
retaining its noncollapse data; Claim 11.35, continuation, printed p. 291. -/
noncomputable def restrictFiniteHorizonSlab
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ} {A T T' kappa r₀ : ℝ}
    (L : M30FiniteHorizonSlab S k A T' kappa r₀) (hTT' : T ≤ T') :
    M30FiniteHorizonSlab S k A T kappa r₀ := by
  have hI : Set.Ioc (-T) 0 ⊆ Set.Ioc (-T') 0 := by
    intro s hs
    exact ⟨(neg_le_neg hTT').trans_lt hs.1, hs.2⟩
  exact {
    embedding := restrictCylinderTime L.embedding hI
    zero_identity := fun hzero x hx => L.zero_identity (hI hzero) x hx
    noncollapsed := fun s hs x hx => L.noncollapsed s (hI hs) x hx }

/-- Eventual slabs at positive cofinal step durations give M30's literal
infinite-horizon controls on the same sequence; Claim 11.35, p. 291. -/
noncomputable def longControls_of_step_slabs
    {S : GeneralizedBlowupSequence.{u}} {epsilon C kappa r₀ mu c : ℝ}
    (H : M30CommonBlowupControls S epsilon C kappa r₀ mu) (hc : 0 < c)
    (hstage : ∀ n : ℕ, ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in Filter.atTop,
      Nonempty (M30FiniteHorizonSlab S k A ((n : ℝ) * c) kappa r₀)) :
    M30LongBlowupControls S epsilon C kappa r₀ mu ⊤ where
  toM30CommonBlowupControls := H
  horizon_pos := by simp
  slabs T _ _ A hA := by
    obtain ⟨n, hn⟩ := exists_nat_gt (T / c)
    have hT : T ≤ (n : ℝ) * c := ((div_lt_iff₀ hc).mp hn).le
    filter_upwards [hstage n A hA] with k hk
    exact hk.map fun L => restrictFiniteHorizonSlab L hT

end PoincareMT.M32
