import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.SectionalAlgebra









set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}



structure CompactSectionalParameters (F : RicciFlow n M J) where
  carrier : Type u
  topology : TopologicalSpace carrier
  compact : CompactSpace carrier
  point : carrier → M
  point_continuous : Continuous point
  left : (z : carrier) → TangentSpace (𝓡 n) (point z)
  right : (z : carrier) → TangentSpace (𝓡 n) (point z)
  independent : ∀ z, LinearIndependent ℝ ![left z, right z]
  complete : ∀ t m : ℝ,
    (∀ z, m * metricGram (F.metric t) (point z) (left z) (right z) ≤
      (F.connection t).curvatureTensor (point z) (left z) (right z) (left z) (right z)) →
    ∀ y : M, ∀ a b : TangentSpace (𝓡 n) y,
      m * metricGram (F.metric t) y a b ≤ (F.connection t).curvatureTensor y a b a b
  complete_on : ∀ U : Set M, ∀ t m : ℝ,
    (∀ z, point z ∈ U →
      m * metricGram (F.metric t) (point z) (left z) (right z) ≤
        (F.connection t).curvatureTensor (point z) (left z) (right z) (left z) (right z)) →
    ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      m * metricGram (F.metric t) y a b ≤ (F.connection t).curvatureTensor y a b a b
  continuous_quotient : ContinuousOn (fun p : ℝ × carrier =>
    (F.connection p.1).curvatureTensor (point p.2) (left p.2) (right p.2)
      (left p.2) (right p.2) /
      metricGram (F.metric p.1) (point p.2) (left p.2) (right p.2)) (J ×ˢ univ)

attribute [instance] CompactSectionalParameters.topology CompactSectionalParameters.compact

set_option maxHeartbeats 1800000 in

set_option backward.isDefEq.respectTransparency false in


theorem compactSectionalParameters [CompactSpace M] (F : RicciFlow n M J) :
    Nonempty (CompactSectionalParameters F) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e := fun c : M => trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
  obtain ⟨s, K, hK, hKe, hcover⟩ := exists_finite_compact_tangent_cover (n := n) (M := M)
  let P := modelOrthonormalPairs n
  let C := (i : s) × (K i.1) × P
  let (c : M) : CompactSpace (K c) := isCompact_iff_compactSpace.mp (hK c)
  let : CompactSpace P := isCompact_iff_compactSpace.mp (isCompact_modelOrthonormalPairs n)
  let : CompactSpace C := inferInstance
  let X : C → M := fun z => z.2.1.1
  let U : (z : C) → TangentSpace (𝓡 n) (X z) :=
    fun z => (e z.1.1).symmL ℝ (X z) z.2.2.1.1
  let V : (z : C) → TangentSpace (𝓡 n) (X z) :=
    fun z => (e z.1.1).symmL ℝ (X z) z.2.2.1.2
  have hX : Continuous X := by
    apply continuous_sigma
    intro i
    exact continuous_subtype_val.comp continuous_fst
  have hlin (z : C) : LinearIndependent ℝ ![U z, V z] := by
    have hp := z.2.2.2
    have horth : Orthonormal ℝ (![z.2.2.1.1, z.2.2.1.2] : Fin 2 → E) := by
      constructor
      · intro i
        fin_cases i
        · exact hp.1
        · exact hp.2.1
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact hp.2.2
        · change inner ℝ z.2.2.1.2 z.2.2.1.1 = 0
          rw [real_inner_comm]
          exact hp.2.2
        · exact (hij rfl).elim
    have hy : X z ∈ (e z.1.1).baseSet := hKe z.1.1 z.2.1.2
    have hinj : Function.Injective ((e z.1.1).symmL ℝ (X z)) := by
      intro a b hab
      have h := congrArg ((e z.1.1).continuousLinearMapAt ℝ (X z)) hab
      simpa only [(e z.1.1).continuousLinearMapAt_symmL hy] using h
    have h := horth.linearIndependent.map' ((e z.1.1).symmL ℝ (X z)).toLinearMap
      (LinearMap.ker_eq_bot.mpr hinj)
    convert! h using 1
    funext i
    fin_cases i <;> rfl
  refine ⟨{
    carrier := C
    topology := inferInstance
    compact := inferInstance
    point := X
    point_continuous := hX
    left := U
    right := V
    independent := hlin
    complete := ?_
    complete_on := ?_
    continuous_quotient := ?_
  }⟩
  · intro t m h y a b
    have hycover : y ∈ ⋃ c ∈ s, K c := hcover ▸ mem_univ y
    obtain ⟨c, hc, hyK⟩ := mem_iUnion₂.mp hycover
    apply sectional_lower_from_model_pairs (F.connection t) c y (hKe c hyK) m _ a b
    intro p hp
    exact h ⟨⟨c, hc⟩, ⟨⟨y, hyK⟩, ⟨p, hp⟩⟩⟩
  · intro S t m h y hy a b
    have hycover : y ∈ ⋃ c ∈ s, K c := hcover ▸ mem_univ y
    obtain ⟨c, hc, hyK⟩ := mem_iUnion₂.mp hycover
    apply sectional_lower_from_model_pairs (F.connection t) c y (hKe c hyK) m _ a b
    intro p hp
    exact h ⟨⟨c, hc⟩, ⟨⟨y, hyK⟩, ⟨p, hp⟩⟩⟩ hy
  · let q : ℝ → C → ℝ := fun t z =>
      (F.connection t).curvatureTensor (X z) (U z) (V z) (U z) (V z) /
        metricGram (F.metric t) (X z) (U z) (V z)
    have hqc : Continuous (fun p : J × C => q p.1 p.2) := by
      let D := (i : s) × ((K i.1) × P) × J
      let d : C × J ≃ₜ D := Homeomorph.sigmaProdDistrib
      have h : Continuous (fun z : D => q z.2.2 ⟨z.1, z.2.1⟩) := by
        apply continuous_sigma
        intro i
        have hp : Continuous (fun p : ((K i.1) × P) × J =>
            (((p.2 : ℝ), (p.1.1 : M)), (p.1.2 : E × E))) := by fun_prop
        exact (continuousOn_flow_sectionalRayleigh_trivialization F i.1).comp_continuous hp
          (fun p => ⟨⟨p.2.2, hKe i.1 p.1.1.2⟩, p.1.2.2⟩)
      have hs : Continuous (fun p : C × J => q p.2 p.1) := h.comp d.continuous
      exact hs.comp continuous_swap
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hmap : Continuous (fun p : J ×ˢ (univ : Set C) =>
        ((⟨p.1.1, p.2.1⟩ : J), p.1.2)) := by fun_prop
    exact hqc.comp hmap

end PoincareConjecture.Proofs.M46
