import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorThirdDerivatives









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

def HasFiniteWeakJet (u : L2) (s : ℕ) : Prop :=
  ∃ q : List (Fin n) → L2, q [] = u ∧ IsWeakSchwartzJet q s

theorem HasFiniteWeakJet.mono {u : L2} {s r : ℕ}
    (hu : HasFiniteWeakJet u s) (hrs : r ≤ s) : HasFiniteWeakJet u r := by
  obtain ⟨q, hq0, hq⟩ := hu
  exact ⟨q, hq0, hq.mono hrs⟩

theorem HasFiniteWeakJet.zero (s : ℕ) : HasFiniteWeakJet (0 : L2) s :=
  ⟨fun _ => 0, rfl, fun _ _ i =>
    HasWeakSchwartzDerivative.zero (EuclideanSpace.single i (1 : ℝ))⟩

theorem HasFiniteWeakJet.add {u v : L2} {s : ℕ}
    (hu : HasFiniteWeakJet u s) (hv : HasFiniteWeakJet v s) :
    HasFiniteWeakJet (u + v) s := by
  obtain ⟨q, hq0, hq⟩ := hu
  obtain ⟨p, hp0, hp⟩ := hv
  exact ⟨fun w => q w + p w, congrArg₂ (· + ·) hq0 hp0,
    fun w hw i => (hq w hw i).add (hp w hw i)⟩

theorem HasFiniteWeakJet.sub {u v : L2} {s : ℕ}
    (hu : HasFiniteWeakJet u s) (hv : HasFiniteWeakJet v s) :
    HasFiniteWeakJet (u - v) s := by
  obtain ⟨q, hq0, hq⟩ := hu
  obtain ⟨p, hp0, hp⟩ := hv
  exact ⟨fun w => q w - p w, congrArg₂ (· - ·) hq0 hp0,
    fun w hw i => weakSchwartzDerivative_sub (hq w hw i) (hp w hw i)⟩

theorem HasFiniteWeakJet.sum {ι : Type*} [Fintype ι] (u : ι → L2) {s : ℕ}
    (hu : ∀ i, HasFiniteWeakJet (u i) s) : HasFiniteWeakJet (∑ i, u i) s := by
  classical
  choose q hq0 hq using hu
  refine ⟨fun w => ∑ i, q i w, Finset.sum_congr rfl (fun i _ => hq0 i), ?_⟩
  intro w hw j
  exact HasWeakSchwartzDerivative.finset_sum Finset.univ _ _ _ (fun i _ => hq i w hw j)

theorem HasFiniteWeakJet.finset_sum {ι : Type*} (T : Finset ι) (u : ι → L2) {s : ℕ}
    (hu : ∀ i ∈ T, HasFiniteWeakJet (u i) s) : HasFiniteWeakJet (∑ i ∈ T, u i) s := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasFiniteWeakJet.zero (n := n) s
  | @insert i T hi ih =>
    rw [Finset.sum_insert hi]
    exact (hu i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

theorem HasFiniteWeakJet.nsmul {u : L2} {s : ℕ}
    (hu : HasFiniteWeakJet u s) (c : ℕ) : HasFiniteWeakJet (c • u) s := by
  induction c with
  | zero => simpa only [zero_smul] using HasFiniteWeakJet.zero (n := n) s
  | succ c ih => simpa only [succ_nsmul] using ih.add hu

theorem HasFiniteWeakJet.mul {u : L2} {s : ℕ}
    (hu : HasFiniteWeakJet u s) (a : 𝓢(V, ℝ)) :
    HasFiniteWeakJet (schwartzMultiplier a u) s := by
  obtain ⟨q, hq0, hq⟩ := hu
  let e : JetExpression n := .term a []
  have he : e.orderLE 0 := Nat.zero_le 0
  refine ⟨fun w => (e.iteratedDerivative w).eval q, ?_, ?_⟩
  · exact congrArg (schwartzMultiplier a) hq0
  · exact e.isWeakJet_eval_iteratedDerivative he q (by simpa only [Nat.add_zero] using hq)

theorem HasFiniteWeakJet.of_derivative {u d : L2} {s : ℕ}
    (hu : HasFiniteWeakJet u (s + 1)) (i : Fin n)
    (hd : HasWeakSchwartzDerivative u d (EuclideanSpace.single i (1 : ℝ))) :
    HasFiniteWeakJet d s := by
  obtain ⟨q, hq0, hq⟩ := hu
  have hi : q [i] = d := by
    have h := hq [] (by simp) i
    rw [hq0] at h
    exact h.unique hd
  refine ⟨fun w => q (w ++ [i]), hi, ?_⟩
  intro w hw j
  have hw' : (w ++ [i]).length < s + 1 := by
    simp only [List.length_append, List.length_singleton]
    omega
  exact hq (w ++ [i]) hw' j

theorem HasFiniteWeakJet.exists_derivative {u : L2} {s : ℕ}
    (hu : HasFiniteWeakJet u (s + 1)) (i : Fin n) :
    ∃ d : L2, HasWeakSchwartzDerivative u d (EuclideanSpace.single i (1 : ℝ)) ∧
      HasFiniteWeakJet d s := by
  obtain ⟨q, hq0, hq⟩ := hu
  have hd : HasWeakSchwartzDerivative u (q [i]) (EuclideanSpace.single i (1 : ℝ)) := by
    simpa only [hq0] using hq [] (by simp) i
  exact ⟨q [i], hd, HasFiniteWeakJet.of_derivative ⟨q, hq0, hq⟩ i hd⟩

def HasInteriorWeakJets (K : Set V) (u : dirichletForm K) (s : ℕ) : Prop :=
  ∀ a : 𝓢(V, ℝ), HasCompactSupport a → tsupport a ⊆ interior K →
    HasFiniteWeakJet (localizedDirichletValue K a u) s

theorem HasInteriorWeakJets.mono {K : Set V} {u : dirichletForm K} {s r : ℕ}
    (hu : HasInteriorWeakJets K u s) (hrs : r ≤ s) : HasInteriorWeakJets K u r :=
  fun a ha haK => (hu a ha haK).mono hrs

theorem hasInteriorWeakJets_one (K : Set V) (u : dirichletForm K) :
    HasInteriorWeakJets K u 1 := by
  intro a _ _
  let q : List (Fin n) → L2
    | [] => localizedDirichletValue K a u
    | i :: _ => localizedDirichletPartial K a u i
  refine ⟨q, rfl, ?_⟩
  intro w hw i
  have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst w
  exact localizedDirichletPartial_weak K a u i

theorem HasInteriorWeakJets.partial_product {K : Set V} {u : dirichletForm K} {s : ℕ}
    (hu : HasInteriorWeakJets K u (s + 1)) (a : 𝓢(V, ℝ))
    (ha : HasCompactSupport a) (haK : tsupport a ⊆ interior K) (i : Fin n) :
    HasFiniteWeakJet (schwartzMultiplier a (dirichletPartial K i u)) s := by
  have hfirst := (hu a ha haK).of_derivative i (localizedDirichletPartial_weak K a u i)
  have had : HasCompactSupport ((∂_{EuclideanSpace.single i (1 : ℝ)} a : 𝓢(V, ℝ)) : V → ℝ) :=
    ha.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset _ _)
  have hadK : tsupport ((∂_{EuclideanSpace.single i (1 : ℝ)} a : 𝓢(V, ℝ)) : V → ℝ) ⊆
      interior K := (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans haK
  have hcut := (hu (∂_{EuclideanSpace.single i (1 : ℝ)} a) had hadK).mono (Nat.le_succ s)
  have h := hfirst.sub hcut
  simpa only [localizedDirichletPartial, localizedDirichletValue, add_sub_cancel_right] using h

end PoincareConjecture.M35.Uniqueness.Heat
