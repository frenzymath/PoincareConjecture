import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoverStepCount













set_option autoImplicit false

universe w z v

open Set Topology

namespace Geometry






theorem FinitePiecewiseAffineOn.exists_strict_two_sheet_neighborhood_count
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : U → V} {D : Set U} (hF : FinitePiecewiseAffineOn F D) (hD : D.Nonempty) :
    ∃ S : Set D, S.Finite ∧
      ∀ (X : Type z) [TopologicalSpace X] (q : X → V), IsLocallyInjective q →
        ∀ (E : Type w) [TopologicalSpace E] [T2Space E] [ConnectedSpace E]
          (p : E → X), IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
          ∀ (Y : Type v) [TopologicalSpace Y] (j : C(Y, E)), Function.Injective j →
            ∀ (f : C(D, X)), (∀ u, q (f u) = F u) →
            ∀ (g : C(D, Y)), (∀ u, p (j (g u)) = f u) →
            ∀ (r : C(X, X)), (ContinuousMap.id X).HomotopyRel r (range f) →
              (∀ x, r x ∈ range f) →
              IsLocallyInjective (q ∘ p ∘ j) ∧
                (f '' S).ncard < (g '' S).ncard ∧ (g '' S).ncard ≤ S.ncard ∧
                  S.ncard - (g '' S).ncard < S.ncard - (f '' S).ncard := by
  obtain ⟨S, hS, hcount⟩ := hF.exists_strict_two_sheet_count hD
  refine ⟨S, hS, ?_⟩
  intro X instX q hq E instE instT2 instConn p hp htwo Y instY j hj
    f hqf g hpg r H hr
  have hjlocal : IsLocallyInjective (j : Y → E) :=
    fun y => ⟨univ, isOpen_univ, mem_univ y, hj.injOn⟩
  have hlocal : IsLocallyInjective (q ∘ p ∘ j) :=
    (hq.comp hp.isLocalHomeomorph.isLocallyInjective hp.continuous).comp
      hjlocal j.continuous
  have himage : ((j.comp g) '' S).ncard = (g '' S).ncard := by
    change ((fun u => j (g u)) '' S).ncard = (g '' S).ncard
    rw [← image_image]
    exact ncard_image_of_injective _ hj
  have hstrict := hcount X q hq E p hp htwo f hqf (j.comp g) hpg r H hr
  rw [himage] at hstrict
  exact ⟨hlocal, hstrict⟩









theorem FinitePiecewiseAffineOn.not_infinite_two_sheet_tower
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : U → V} {D : Set U} (hF : FinitePiecewiseAffineOn F D) (hD : D.Nonempty)
    (X E : ℕ → Type w) [∀ n, TopologicalSpace (X n)]
    [∀ n, TopologicalSpace (E n)] [∀ n, T2Space (E n)] [∀ n, ConnectedSpace (E n)]
    (q : ∀ n, X n → V) (hq : ∀ n, IsLocallyInjective (q n))
    (p : ∀ n, E n → X n) (hp : ∀ n, IsCoveringMap (p n))
    (htwo : ∀ n x, (p n ⁻¹' {x}).ncard = 2)
    (j : ∀ n, C(X (n + 1), E n)) (hj : ∀ n, Function.Injective (j n))
    (f : ∀ n, C(D, X n)) (hqf : ∀ n u, q n (f n u) = F u)
    (hpf : ∀ n u, p n (j n (f (n + 1) u)) = f n u)
    (r : ∀ n, C(X n, X n))
    (H : ∀ n, (ContinuousMap.id (X n)).HomotopyRel (r n) (range (f n)))
    (hr : ∀ n x, r n x ∈ range (f n)) : False := by
  obtain ⟨S, hS, hcount⟩ := hF.exists_strict_two_sheet_neighborhood_count hD
  let c : ℕ → ℕ := fun n => (f n '' S).ncard
  have hstep (n : ℕ) : c n < c (n + 1) :=
    (hcount (X n) (q n) (hq n) (E n) (p n) (hp n) (htwo n)
      (X (n + 1)) (j n) (hj n) (f n) (hqf n) (f (n + 1)) (hpf n)
      (r n) (H n) (hr n)).2.1
  have hlower (n : ℕ) : n ≤ c n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hstep n))
  have hupper (n : ℕ) : c n ≤ S.ncard := ncard_image_le hS
  exact Nat.not_succ_le_self S.ncard
    ((hlower (S.ncard + 1)).trans (hupper (S.ncard + 1)))

end Geometry
