import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Set.Card











set_option autoImplicit false

open Set Geometry

namespace Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]




theorem IsFinitePLBallPair.exists_boundary_eq_pair {d b : Set X}
    (hd : IsFinitePLBallPair ℝ d b) :
    ∃ x y : X, x ≠ y ∧ b = {x, y} := by
  obtain ⟨hb, C, hC, hcv, hne, e, _, heb⟩ := hd
  have hCI : C = Icc (sInf C) (sSup C) :=
    eq_Icc_of_connected_compact (hcv.isConnected (hne.mono interior_subset)) hC
  have hlt : sInf C < sSup C := by
    rw [hCI, interior_Icc] at hne
    exact nonempty_Ioo.mp hne
  have hfront : frontier C = {sInf C, sSup C} :=
    (congrArg frontier hCI).trans (frontier_Icc hlt.le)
  let a : C := ⟨sInf C, hCI.symm.subset ⟨le_rfl, hlt.le⟩⟩
  let z : C := ⟨sSup C, hCI.symm.subset ⟨hlt.le, le_rfl⟩⟩
  let x := e.symm a
  let y := e.symm z
  have hxy : (x : X) ≠ (y : X) := by
    intro h
    have h' : x = y := Subtype.ext h
    have h'' := congrArg (fun w : d => (e w : ℝ)) h'
    change (e (e.symm a) : ℝ) = (e (e.symm z) : ℝ) at h''
    rw [e.apply_symm_apply, e.apply_symm_apply] at h''
    exact hlt.ne h''
  refine ⟨x, y, hxy, ?_⟩
  ext w
  constructor
  · intro hw
    have hwf := (heb ⟨w, hb hw⟩).mp hw
    rw [hfront] at hwf
    rcases hwf with hwf | hwf
    · have hew : e ⟨w, hb hw⟩ = a := Subtype.ext hwf
      have h := congrArg (fun u : C => (e.symm u : X)) hew
      exact Or.inl (by simpa only [e.symm_apply_apply] using h)
    · have hew : e ⟨w, hb hw⟩ = z := Subtype.ext hwf
      have h := congrArg (fun u : C => (e.symm u : X)) hew
      refine Or.inr ?_
      change w = (e.symm z : X)
      simpa only [e.symm_apply_apply] using h
  · rintro (rfl | rfl)
    · apply (heb x).mpr
      change (e (e.symm a) : ℝ) ∈ frontier C
      rw [e.apply_symm_apply, hfront]
      exact Or.inl rfl
    · apply (heb y).mpr
      change (e (e.symm z) : ℝ) ∈ frontier C
      rw [e.apply_symm_apply, hfront]
      exact Or.inr rfl



theorem IsFinitePLBallPair.ncard_boundary_eq_two {d b : Set X}
    (hd : IsFinitePLBallPair ℝ d b) : b.ncard = 2 := by
  obtain ⟨x, y, hxy, rfl⟩ := hd.exists_boundary_eq_pair
  exact ncard_pair hxy





theorem exists_single_interval_of_ncard_boundary_iUnion_eq_two {ι : Type*}
    (D B : ι → Set X) (hball : ∀ i, IsFinitePLBallPair ℝ (D i) (B i))
    (hdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (htwo : (⋃ i, B i).ncard = 2) :
    ∃ i, (∀ j, j = i) ∧ (⋃ j, D j) = D i ∧ (⋃ j, B j) = B i := by
  classical
  obtain ⟨a, b, _, hpair⟩ := ncard_eq_two.mp htwo
  have hfinite : (⋃ i, B i).Finite := hpair.symm ▸ (finite_singleton b).insert a
  have ha : a ∈ ⋃ i, B i := hpair.symm ▸ (show a ∈ ({a, b} : Set X) from Or.inl rfl)
  obtain ⟨i, hai⟩ := mem_iUnion.mp ha
  have hfull (j : ι) : B j = ⋃ k, B k :=
    eq_of_subset_of_ncard_le (subset_iUnion B j)
      (by rw [htwo, (hball j).ncard_boundary_eq_two]) hfinite
  have huniq (j : ι) : j = i := by
    by_contra hji
    exact disjoint_left.mp (hdisj hji)
      ((hball j).1 ((hfull j).symm ▸ ha)) ((hball i).1 hai)
  refine ⟨i, huniq, ?_, (hfull i).symm⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    exact huniq j ▸ hxj
  · exact subset_iUnion D i

end Set
