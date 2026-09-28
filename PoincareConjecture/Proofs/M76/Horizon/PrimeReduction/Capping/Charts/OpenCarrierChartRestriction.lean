import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.FinitePLCarrierChartCompatibility

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

theorem exists_open_carrier_restriction
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {T V : Set X} (hVT : V ⊆ T)
    (hV : IsOpen ((Subtype.val : T → X) ⁻¹' V))
    (Q : OpenPartialHomeomorph T Y) (p : V)
    (hp : (⟨p, hVT p.property⟩ : T) ∈ Q.source) :
    ∃ q : OpenPartialHomeomorph V Y,
      q.source = (fun x : V => (⟨x, hVT x.property⟩ : T)) ⁻¹' Q.source ∧
      q.target = Q.target ∩ {y | (Q.symm y : X) ∈ V} ∧
      p ∈ q.source ∧
      (∀ x : V, q x = Q ⟨x, hVT x.property⟩) ∧
      ∀ y ∈ q.target, (q.symm y : X) = (Q.symm y : X) := by
  let U : TopologicalSpace.Opens T := ⟨(Subtype.val : T → X) ⁻¹' V, hV⟩
  let H : V ≃ₜ U := {
    toFun := fun x => ⟨⟨x, hVT x.property⟩, x.property⟩
    invFun := fun x => ⟨(x : T), x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let hU : Nonempty U := ⟨H p⟩
  let q := H.toOpenPartialHomeomorph.trans (Q.subtypeRestr hU)
  refine ⟨q, ?_, ?_, ?_, fun _ => rfl, ?_⟩
  · ext x
    change (x ∈ Set.univ ∧ H x ∈ (Q.subtypeRestr hU).source) ↔ _
    simp only [mem_univ, true_and, subtypeRestr_source, mem_preimage]
    rfl
  · ext y
    change (y ∈ (Q.subtypeRestr hU).target ∧
      (Q.subtypeRestr hU).symm y ∈ Set.univ) ↔ _
    simp only [mem_univ, and_true]
    simp only [subtypeRestr_def, trans_target,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    rfl
  · refine ⟨mem_univ _, ?_⟩
    change H p ∈ (Q.subtypeRestr hU).source
    rw [subtypeRestr_source]
    exact hp
  · intro y hy
    have hy' : y ∈ (Q.subtypeRestr hU).target := hy.1
    exact congrArg Subtype.val (Q.subtypeRestr_symm_apply hU hy')

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_compatible_open_carrier_charts
    {T V : Set E} (hVT : V ⊆ T)
    (hV : IsOpen ((Subtype.val : T → E) ⁻¹' V))
    (Q : V → OpenPartialHomeomorph T F)
    (A : V → Set E) (C : V → Set F) (f : V → E → F) (g : V → F → E)
    (hp : ∀ p : V, (⟨p, hVT p.property⟩ : T) ∈ (Q p).source)
    (hf : ∀ p, FinitePiecewiseAffineOn (f p) (A p))
    (hg : ∀ p, FinitePiecewiseAffineOn (g p) (C p))
    (hQs : ∀ p x, x ∈ (Q p).source → (x : E) ∈ A p)
    (hQt : ∀ p, (Q p).target ⊆ interior (C p))
    (hQf : ∀ p x, x ∈ (Q p).source → Q p x = f p x)
    (hQg : ∀ p y, y ∈ (Q p).target → ((Q p).symm y : E) = g p y) :
    ∃ q : V → OpenPartialHomeomorph V F,
      (∀ p, p ∈ (q p).source) ∧
      (∀ p r, (q p).symm.trans (q r) ∈ piecewiseAffineGroupoid F) ∧
      (∀ p, (q p).source =
        (fun x : V => (⟨x, hVT x.property⟩ : T)) ⁻¹' (Q p).source) ∧
      (∀ p, (q p).target = (Q p).target ∩ {y | ((Q p).symm y : E) ∈ V}) ∧
      (∀ p x, x ∈ (q p).source → q p x = f p x) ∧
      ∀ p y, y ∈ (q p).target → ((q p).symm y : E) = g p y := by
  classical
  choose q hqs hqt hqp hqf hqg using
    fun p : V => exists_open_carrier_restriction hVT hV (Q p) p (hp p)
  have hforward (p : V) (x : V) (hx : x ∈ (q p).source) : q p x = f p x := by
    rw [hqf]
    rw [hqs p] at hx
    exact hQf p _ hx
  have hinverse (p : V) (y : F) (hy : y ∈ (q p).target) :
      ((q p).symm y : E) = g p y :=
    (hqg p y hy).trans (hQg p y (((hqt p) ▸ hy).1))
  refine ⟨q, hqp, ?_, hqs, hqt, hforward, hinverse⟩
  intro p r
  apply (q p).mem_piecewiseAffineGroupoid_transition_of_finitePL_representatives
    (q r) (hf r) (hg p)
  · intro x hx
    exact hQs r _ ((hqs r) ▸ hx)
  · intro y hy
    exact hQt p (((hqt p) ▸ hy).1)
  · exact hforward r
  · exact hinverse p

end OpenPartialHomeomorph
