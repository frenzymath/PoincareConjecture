import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.FaceData

set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_relative_finite_face_history
    {s t : Stage e S f r C} (step : Step s t)
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {n : ℕ} (face : Fin n → Finset V) (hfaces : ∀ i, face i ∈ K.faces)
    (P : ℕ → SimplicialComplex ℝ V) (hmon : Monotone P)
    (hPK : ∀ k ≤ n, P k ≤ K)
    (hsucc : ∀ i : Fin n,
      (P (i.val + 1)).space = (P i.val).space ∪ convexHull ℝ (face i : Set V))
    (R : Set M) (boundary : Set V)
    (Q : Fin n → OpenPartialHomeomorph t.Carrier E)
    (B : Fin n → OpenPartialHomeomorph s.Carrier E)
    (J : Fin n → SimplicialComplex ℝ E)
    (hQ : ∀ i k, (t.charts k).symm.trans (Q i) ∈ piecewiseAffineGroupoid E)
    (hB : ∀ i k, (s.charts k).symm.trans (B i) ∈ piecewiseAffineGroupoid E)
    (hJ : ∀ i, (J i).faces.Finite) (hcv : ∀ i, Convex ℝ (J i).space)
    (hJQ : ∀ i, (J i).space ⊆ (Q i).target)
    (hJB : ∀ i, (J i).space ⊆ (B i).target)
    (hinside : ∀ i, (Q i).source ⊆ interior (t.projection ⁻¹' R))
    (N : K.faces → Set t.Carrier) (hN : ∀ a, IsOpen (N a))
    (hselected : ∀ i, N ⟨face i, hfaces i⟩ ⊆
      (Q i).source ∩ (Q i) ⁻¹' interior (J i).space)
    (initial : RelativeSurfaceState t K N R boundary) :
    ∃ states : ℕ → RelativeSurfaceState t K N R boundary,
      states 0 = initial ∧
      (∀ i (hi : i < n),
        ∃ motion : RelativeFaceMotionData step K (P i) (P (i + 1)) (states i).map
          (Q ⟨i, hi⟩) (B ⟨i, hi⟩) (J ⟨i, hi⟩) N R,
          (states (i + 1)).map = motion.ambient 1 ∘ (states i).map) ∧
      (∀ i k, i ≤ k → k ≤ n → EqOn (states k).map (states i).map (P i).space) ∧
      ∀ k ≤ n, EqOn (states k).map initial.map (P 0).space := by
  classical
  have hbuild : ∀ m (hm : m ≤ n),
      ∃ states : ℕ → RelativeSurfaceState t K N R boundary,
        states 0 = initial ∧ ∀ i (hi : i < m),
          ∃ motion : RelativeFaceMotionData step K (P i) (P (i + 1)) (states i).map
            (Q ⟨i, hi.trans_le hm⟩) (B ⟨i, hi.trans_le hm⟩) (J ⟨i, hi.trans_le hm⟩) N R,
            (states (i + 1)).map = motion.ambient 1 ∘ (states i).map := by
    intro m
    induction m with
    | zero =>
      intro hm
      refine ⟨fun _ ↦ initial, rfl, ?_⟩
      intro i hi
      exact False.elim (Nat.not_lt_zero i hi)
    | succ m ih =>
      intro hm
      have hmn : m < n := by omega
      let a : Fin n := ⟨m, hmn⟩
      obtain ⟨states, hzero, hsteps⟩ := ih (by omega)
      have hfree : ∀ x ∈ convexHull ℝ (face a : Set V),
          x ∉ (P m).space → Q a ((states m).map x) ∈ interior (J a).space := by
        intro x hx _
        exact (hselected a ((states m).retained ⟨face a, hfaces a⟩ hx)).2
      obtain ⟨motion⟩ := step.nonempty_relative_face_motion_data K (P m) (P (m + 1)) hK
        (hmon (Nat.le_succ m)) (hPK _ hm) (states m) (face a) (hsucc a)
        (Q a) (B a) (hQ a) (hB a) (J a) (hJ a) (hcv a) (hJQ a) (hJB a)
        hfree (hinside a) hN
      let next := (states m).move hK motion
      let states' : ℕ → RelativeSurfaceState t K N R boundary :=
        Function.update states (m + 1) next
      have hsame (i : ℕ) (hi : i ≤ m) : states' i = states i :=
        Function.update_of_ne (a := i) (a' := m + 1) (by omega) next states
      have hnext : states' (m + 1) = next := Function.update_self _ _ _
      refine ⟨states', (hsame 0 (Nat.zero_le m)).trans hzero, ?_⟩
      intro i hi
      by_cases him : i = m
      · subst i
        rw [hsame m le_rfl, hnext]
        exact ⟨motion, rfl⟩
      · have him' : i < m := by omega
        rw [hsame i (by omega), hsame (i + 1) (by omega)]
        exact hsteps i him'
  obtain ⟨states, hzero, hsteps⟩ := hbuild n le_rfl
  have hprefix : ∀ i k, i ≤ k → k ≤ n →
      EqOn (states k).map (states i).map (P i).space := by
    intro i k hik
    induction k, hik using Nat.le_induction with
    | base =>
      intro _
      exact fun _ _ ↦ rfl
    | succ k hik ih =>
      intro hkn
      obtain ⟨motion, htransition⟩ := hsteps k (by omega)
      intro x hx
      have hxk : x ∈ (P k).space := SimplicialComplex.space_subset_of_le (hmon hik) hx
      have hfix : motion.ambient 1 ((states k).map x) = (states k).map x :=
        motion.prefix_fixed 1 (mem_image_of_mem (states k).map hxk)
      calc
        (states (k + 1)).map x = motion.ambient 1 ((states k).map x) :=
          congrFun htransition x
        _ = (states k).map x := hfix
        _ = (states i).map x := ih (by omega) hx
  refine ⟨states, hzero, hsteps, hprefix, ?_⟩
  intro k hk
  simpa only [hzero] using hprefix 0 k (Nat.zero_le k) hk

end Geometry.OriginalPLTower
