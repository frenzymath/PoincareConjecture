import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.CapCompactness
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial
import PoincareLib.Topology.Manifold.NeckCap.Theory

/-!
# Neck-and-cap covers of high-curvature terminal tails

Canonical control on a noncompact terminal component has only the neck and
cap alternatives. A high-curvature end tail therefore gives the connected
cover required by the supplied Appendix A theory.
Reference: Morgan--Tian, Lemma 11.28, pp. 285--287.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}

/-- Connected regions of a terminal component carrying an end have the
neck-and-cap cover of Appendix A;
compact canonical alternatives are excluded by the existence of the end. -/
noncomputable def neckCapCoverOn (e : TerminalEnd K)
    (X : Set (E.extended.slice T).carrier) (hX : IsConnected X) (hXK : X ⊆ K.component)
    {epsilon C epsilon₀ : ℝ} (hepsilon : 0 < epsilon) (hC : 0 < C)
    (hthreshold : 0 < epsilon₀) (hsmall : epsilon₀ ≤ 1 / 200)
    (hle : epsilon ≤ epsilon₀)
    (hcanonical : ∀ x ∈ X,
      GeneralizedCanonicalControl (F := E.extended) T x epsilon C) :
    ConnectedNeckCapCover (E.extended.metric T) where
  epsilon := epsilon
  epsilon_pos := hepsilon
  epsilon_threshold := epsilon₀
  epsilon_threshold_pos := hthreshold
  epsilon_threshold_le_one_two_hundred := hsmall
  epsilon_le_threshold := hle
  cap_constant := C
  cap_constant_pos := hC
  X := X
  connected_X := hX
  necks := Set.range (fun N : TerminalStrongNeck E epsilon =>
    N.spatialNeck (by linarith))
  caps := {N | N.epsilon = epsilon ∧ N.cap_constant ≤ C ∧
    N.connection = E.extended.connection T}
  pointwise_cover := by
    intro x hx
    have hxK : x ∈ K.component := hXK hx
    cases hcanonical x hx with
    | neck N hcenter =>
        exact Or.inl ⟨N.spatialNeck (by linarith), ⟨N, rfl⟩, hcenter⟩
    | cap N he hC hD hxN => exact Or.inr ⟨N, ⟨he, hC, hD⟩, hxN⟩
    | component N hxN => exact (e.not_mem_cComponent N hxK hxN).elim
    | round N hxN => exact (e.not_mem_roundComponent N hxK hxN).elim
  neck_epsilon := by rintro _ ⟨N, rfl⟩; rfl
  cap_epsilon := fun _ hN => hN.1
  cap_constant_bound := fun _ hN => hN.2.1

/-- The connected cover specialized to a whole terminal end tail. -/
noncomputable def neckCapCover (e : TerminalEnd K) (n : ℕ)
    {epsilon C epsilon₀ : ℝ} (hepsilon : 0 < epsilon) (hC : 0 < C)
    (hthreshold : 0 < epsilon₀) (hsmall : epsilon₀ ≤ 1 / 200)
    (hle : epsilon ≤ epsilon₀)
    (hcanonical : ∀ x ∈ Subtype.val '' e.tail n,
      GeneralizedCanonicalControl (F := E.extended) T x epsilon C) :
    ConnectedNeckCapCover (E.extended.metric T) :=
  e.neckCapCoverOn (Subtype.val '' e.tail n) (e.tail_image_connected n)
    (by rintro _ ⟨x, _, rfl⟩; exact x.property)
    hepsilon hC hthreshold hsmall hle hcanonical

/-- Terminal scalar escape puts a whole connected end tail inside the
canonical range, producing a cover at the supplied universal threshold. -/
theorem exists_neckCapCover (e : TerminalEnd K)
    {epsilon C epsilon₀ B : ℝ} (hepsilon : 0 < epsilon) (hC : 0 < C)
    (hthreshold : 0 < epsilon₀) (hsmall : epsilon₀ ≤ 1 / 200)
    (hle : epsilon ≤ epsilon₀)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D))
    (hcanonical : ∀ x : (E.extended.slice T).carrier,
      B < (E.extended.connection T).scalarCurvature x →
        GeneralizedCanonicalControl (F := E.extended) T x epsilon C) :
    ∃ n : ℕ, ∃ H : ConnectedNeckCapCover (E.extended.metric T),
      H.X = Subtype.val '' e.tail n ∧ H.epsilon = epsilon ∧ H.cap_constant = C := by
  obtain ⟨n, hn⟩ := e.exists_tail_scalar_gt hlower hproper B
  have hcontrol : ∀ x ∈ Subtype.val '' e.tail n,
      GeneralizedCanonicalControl (F := E.extended) T x epsilon C := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcanonical x (hn n le_rfl x hx)
  exact ⟨n, e.neckCapCover n hepsilon hC hthreshold hsmall hle hcontrol, rfl, rfl, rfl⟩

end PoincareMT.TerminalEnd
