import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialValueRestriction

/-!
# The actual initial-value survival domain

Morgan-Tian Definition 6.17 and Lemma 6.18, pp. 113-114.
The domain consists of actual frozen initial-value solutions at positive
square times, together with every initial vector at zero. Restriction
proves order-connectedness without assuming local existence or openness.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

/-- Positive square-time survival means existence of an actual frozen
initial-value path, Definition 6.17, p. 113. -/
def initialValueSurvives (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : G.Point) (Z : G.Horizontal x) (s : ℝ) : Prop :=
  0 < s ∧ ∃ y : G.Point, Nonempty (M14SquareRootInitialValuePath G T (s ^ 2) x y Z)

/-- The actual survival domain includes all zero-time initial data,
Definition 6.17 and Lemma 6.18, pp. 113-114. -/
def initialValueDomain (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : G.Point) : Set (G.Horizontal x × ℝ) :=
  {z | z.2 = 0 ∨ initialValueSurvives G T x z.1 z.2}

/-- Select an actual surviving endpoint and use the basepoint elsewhere.
Uniqueness will give coherence, as in Lemma 6.18, pp. 113-114. -/
noncomputable def initialValueCurve (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : G.Point) (Z : G.Horizontal x) (s : ℝ) : G.Point := by
  classical
  exact if h : initialValueSurvives G T x Z s then Classical.choose h.2 else x

variable {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point} {Z : G.Horizontal x} {r s : ℝ}

/-- The chosen endpoint is witnessed by an actual frozen initial-value
path, including its prescribed velocity, Definition 6.17, p. 113. -/
noncomputable def selectedInitialValuePath (hs : initialValueSurvives G T x Z s) :
    M14SquareRootInitialValuePath G T (s ^ 2) x (initialValueCurve G T x Z s) Z := by
  classical
  simpa only [initialValueCurve, dif_pos hs] using Classical.choice (Classical.choose_spec hs.2)

/-- Every initial vector belongs to the survival domain at zero,
Definition 6.17, p. 113. -/
theorem initialValueDomain_zero (Z : G.Horizontal x) :
    (Z, 0) ∈ initialValueDomain G T x := Or.inl rfl

/-- The selected square curve starts at the given basepoint,
Definition 6.17, p. 113. -/
theorem initialValueCurve_zero (Z : G.Horizontal x) :
    initialValueCurve G T x Z 0 = x := by
  unfold initialValueCurve
  rw [dif_neg (show ¬ initialValueSurvives G T x Z 0 from fun h => (lt_irrefl 0) h.1)]

/-- At positive square time the domain is exactly actual initial-value
survival, Definition 6.17 and Lemma 6.18, pp. 113-114. -/
theorem initialValueDomain_positive_iff (hs : 0 < s) :
    (Z, s) ∈ initialValueDomain G T x ↔
      ∃ y : G.Point, Nonempty (M14SquareRootInitialValuePath G T (s ^ 2) x y Z) := by
  simp only [initialValueDomain, mem_ofPred_eq, initialValueSurvives, ne_of_gt hs, false_or,
    hs, true_and]

/-- No negative square time survives, Definition 6.17, p. 113. -/
theorem initialValueDomain_nonneg (hs : (Z, s) ∈ initialValueDomain G T x) : 0 ≤ s := by
  rcases hs with hs | hs
  · exact hs ▸ le_rfl
  · exact hs.1.le

/-- The actual endpoint clock agrees with square-time substitution on
the entire survival domain, Definition 6.17, p. 113. -/
theorem initialValueCurve_clock (hbase : G.spacetime.timeFunction x = T)
    (hs : (Z, s) ∈ initialValueDomain G T x) :
    G.spacetime.timeFunction (initialValueCurve G T x Z s) = T - s ^ 2 := by
  rcases hs with hs | hs
  · change s = 0 at hs
    subst s
    simp only [initialValueCurve_zero, hbase, zero_pow (by decide : 2 ≠ 0), sub_zero]
  · exact (selectedInitialValuePath hs).path.endpoint_time

/-- Every surviving parameter is physically admissible, using the
actual spacetime clock range, Definition 6.17, p. 113. -/
theorem initialValueDomain_admissible (hbase : G.spacetime.timeFunction x = T) :
    initialValueDomain G T x ⊆ M14AdmissibleParameter G T x := by
  intro z hz
  refine ⟨initialValueDomain_nonneg hz, ?_⟩
  rw [← G.spacetime.time_range]
  exact ⟨initialValueCurve G T x z.1 z.2, initialValueCurve_clock hbase hz⟩

/-- An actual surviving solution restricts to every nonnegative earlier
square time, Definition 6.17 and Lemma 6.18, pp. 113-114. -/
theorem initialValueDomain_prefix (hs : (Z, s) ∈ initialValueDomain G T x)
    (hr : 0 ≤ r) (hrs : r ≤ s) : (Z, r) ∈ initialValueDomain G T x := by
  rcases eq_or_lt_of_le hr with hr | hr
  · exact Or.inl hr.symm
  · have hpos : 0 < s := hr.trans_le hrs
    obtain ⟨y, ⟨P⟩⟩ := (initialValueDomain_positive_iff hpos).mp hs
    exact Or.inr ⟨hr, exists_initialValuePath_prefix P (sq_pos_of_pos hr)
      ((sq_le_sq₀ hr.le hpos.le).mpr hrs)⟩

/-- The actual survival times of each initial vector form an
order-connected set, Lemma 6.18, pp. 113-114. -/
theorem initialValueDomain_ordConnected (Z : G.Horizontal x) :
    OrdConnected {s | (Z, s) ∈ initialValueDomain G T x} := by
  constructor
  intro a ha b hb r hr
  exact initialValueDomain_prefix hb ((initialValueDomain_nonneg ha).trans hr.1) hr.2

end PoincareMT.M14
