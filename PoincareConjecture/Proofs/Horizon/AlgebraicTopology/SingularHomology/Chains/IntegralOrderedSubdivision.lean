import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Chains.IntegralOrderedChains








set_option autoImplicit false

noncomputable section

open scoped BigOperators

universe u v

namespace Poincare.Topology

def integralOrderedSubdivision {V : Type u}
    (b : ∀ n : Nat, (Fin (n + 1) → V) → V) (k : Nat) :
    integralOrderedChains V k →ₗ[Int] integralOrderedChains V k :=
  Nat.rec (motive := fun k => integralOrderedChains V k →ₗ[Int] integralOrderedChains V k)
    LinearMap.id
    (fun k S => Finsupp.lsum Int (fun v : Fin (k + 1) → V =>
      (LinearMap.id : Int →ₗ[Int] Int).smulRight
        (integralOrderedCone k (b k v)
          (S (integralOrderedBoundary V k (Finsupp.single v 1)))))) k

def integralOrderedPrism {V : Type u}
    (b : ∀ n : Nat, (Fin (n + 1) → V) → V) (k : Nat) :
    integralOrderedChains V k →ₗ[Int] integralOrderedChains V (k + 1) :=
  Nat.rec (motive := fun k =>
      integralOrderedChains V k →ₗ[Int] integralOrderedChains V (k + 1))
    0
    (fun k T => Finsupp.lsum Int (fun v : Fin (k + 1) → V =>
      (LinearMap.id : Int →ₗ[Int] Int).smulRight
        (integralOrderedCone (k + 1) (b k v)
          (Finsupp.single v 1 -
            integralOrderedSubdivision b (k + 1) (Finsupp.single v 1) -
            T (integralOrderedBoundary V k (Finsupp.single v 1)))))) k

variable {V : Type u}
variable (b : ∀ n : Nat, (Fin (n + 1) → V) → V)

theorem integralOrderedSubdivision_zero :
    integralOrderedSubdivision b 0 = LinearMap.id := rfl

theorem integralOrderedSubdivision_single_succ (k : Nat)
    (v : Fin (k + 1) → V) :
    integralOrderedSubdivision b (k + 1) (Finsupp.single v 1) =
      integralOrderedCone k (b k v)
        (integralOrderedSubdivision b k
          (integralOrderedBoundary V k (Finsupp.single v 1))) := by
  simp [integralOrderedSubdivision, Finsupp.lsum_single, LinearMap.smulRight_apply]

theorem integralOrderedPrism_zero : integralOrderedPrism b 0 = 0 := rfl

theorem integralOrderedPrism_single_succ (k : Nat)
    (v : Fin (k + 1) → V) :
    integralOrderedPrism b (k + 1) (Finsupp.single v 1) =
      integralOrderedCone (k + 1) (b k v)
        (Finsupp.single v 1 -
          integralOrderedSubdivision b (k + 1) (Finsupp.single v 1) -
          integralOrderedPrism b k
            (integralOrderedBoundary V k (Finsupp.single v 1))) := by
  simp [integralOrderedPrism, Finsupp.lsum_single, LinearMap.smulRight_apply]

theorem integralOrderedSubdivision_one
    (hb : ∀ v : Fin 1 → V, b 0 v = v 0) :
    integralOrderedSubdivision b 1 = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro v
  apply LinearMap.ext_ring
  change integralOrderedSubdivision b 1 (Finsupp.single v 1) = Finsupp.single v 1
  rw [integralOrderedSubdivision_single_succ, integralOrderedSubdivision_zero]
  change integralOrderedCone 0 (b 0 v)
    (integralOrderedBoundary V 0 (Finsupp.single v 1)) = Finsupp.single v 1
  rw [integralOrderedBoundary_single, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, integralOrderedCone_single, hb]
  apply congrArg (fun t : Fin 1 → V => Finsupp.single t (1 : Int))
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

theorem integralOrderedPrism_one
    (hb : ∀ v : Fin 1 → V, b 0 v = v 0) :
    integralOrderedPrism b 1 = 0 := by
  apply Finsupp.lhom_ext'
  intro v
  apply LinearMap.ext_ring
  change integralOrderedPrism b 1 (Finsupp.single v 1) = 0
  rw [integralOrderedPrism_single_succ, integralOrderedSubdivision_one b hb,
    integralOrderedPrism_zero]
  simp

theorem integralOrderedSubdivision_boundary (k : Nat)
    (c : integralOrderedChains V (k + 1)) :
    integralOrderedBoundary V k (integralOrderedSubdivision b (k + 1) c) =
      integralOrderedSubdivision b k (integralOrderedBoundary V k c) := by
  induction k with
  | zero =>
      have h : (integralOrderedBoundary V 0).comp (integralOrderedSubdivision b 1) =
          (integralOrderedSubdivision b 0).comp (integralOrderedBoundary V 0) := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedBoundary V 0
          (integralOrderedSubdivision b 1 (Finsupp.single v 1)) =
            integralOrderedSubdivision b 0
              (integralOrderedBoundary V 0 (Finsupp.single v 1))
        rw [integralOrderedSubdivision_single_succ, integralOrderedBoundary_cone_zero]
      exact LinearMap.congr_fun h c
  | succ k ih =>
      have h : (integralOrderedBoundary V (k + 1)).comp
          (integralOrderedSubdivision b (k + 2)) =
          (integralOrderedSubdivision b (k + 1)).comp
            (integralOrderedBoundary V (k + 1)) := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedBoundary V (k + 1)
          (integralOrderedSubdivision b (k + 2) (Finsupp.single v 1)) =
            integralOrderedSubdivision b (k + 1)
              (integralOrderedBoundary V (k + 1) (Finsupp.single v 1))
        rw [integralOrderedSubdivision_single_succ, integralOrderedBoundary_cone_succ,
          ih, integralOrderedBoundary_boundary, map_zero, map_zero, sub_zero]
      exact LinearMap.congr_fun h c

theorem integralOrderedPrism_boundary (k : Nat)
    (c : integralOrderedChains V (k + 1)) :
    integralOrderedBoundary V (k + 1) (integralOrderedPrism b (k + 1) c) +
      integralOrderedPrism b k (integralOrderedBoundary V k c) =
        c - integralOrderedSubdivision b (k + 1) c := by
  induction k with
  | zero =>
      have h : (integralOrderedBoundary V 1).comp (integralOrderedPrism b 1) +
          (integralOrderedPrism b 0).comp (integralOrderedBoundary V 0) =
          LinearMap.id - integralOrderedSubdivision b 1 := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedBoundary V 1
            (integralOrderedPrism b 1 (Finsupp.single v 1)) +
          integralOrderedPrism b 0 (integralOrderedBoundary V 0 (Finsupp.single v 1)) =
            Finsupp.single v 1 - integralOrderedSubdivision b 1 (Finsupp.single v 1)
        rw [integralOrderedPrism_single_succ, integralOrderedPrism_zero]
        simp only [LinearMap.zero_apply, sub_zero, add_zero]
        have hz : integralOrderedBoundary V 0
            (Finsupp.single v 1 - integralOrderedSubdivision b 1 (Finsupp.single v 1)) =
            0 := by
          rw [map_sub, integralOrderedSubdivision_boundary, integralOrderedSubdivision_zero]
          exact sub_self _
        rw [integralOrderedBoundary_cone_succ, hz, map_zero, sub_zero]
      exact LinearMap.congr_fun h c
  | succ k ih =>
      have h : (integralOrderedBoundary V (k + 2)).comp
          (integralOrderedPrism b (k + 2)) +
          (integralOrderedPrism b (k + 1)).comp (integralOrderedBoundary V (k + 1)) =
          LinearMap.id - integralOrderedSubdivision b (k + 2) := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedBoundary V (k + 2)
            (integralOrderedPrism b (k + 2) (Finsupp.single v 1)) +
          integralOrderedPrism b (k + 1)
            (integralOrderedBoundary V (k + 1) (Finsupp.single v 1)) =
          Finsupp.single v 1 - integralOrderedSubdivision b (k + 2) (Finsupp.single v 1)
        have ht := ih (integralOrderedBoundary V (k + 1) (Finsupp.single v 1))
        rw [integralOrderedBoundary_boundary, map_zero, add_zero] at ht
        have hz : integralOrderedBoundary V (k + 1)
            (Finsupp.single v 1 - integralOrderedSubdivision b (k + 2) (Finsupp.single v 1) -
              integralOrderedPrism b (k + 1)
                (integralOrderedBoundary V (k + 1) (Finsupp.single v 1))) = 0 := by
          rw [map_sub, map_sub, integralOrderedSubdivision_boundary, ht, sub_self]
        rw [integralOrderedPrism_single_succ, integralOrderedBoundary_cone_succ,
          hz, map_zero, sub_zero, sub_add_cancel]
      exact LinearMap.congr_fun h c

theorem integralOrderedSubdivision_map {W : Type v}
    (bW : ∀ n : Nat, (Fin (n + 1) → W) → W) (f : V → W)
    (hb : ∀ (n : Nat) (v : Fin (n + 1) → V), f (b n v) = bW n (f ∘ v))
    (k : Nat) (c : integralOrderedChains V k) :
    integralOrderedMap k f (integralOrderedSubdivision b k c) =
      integralOrderedSubdivision bW k (integralOrderedMap k f c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h : (integralOrderedMap (k + 1) f).comp (integralOrderedSubdivision b (k + 1)) =
          (integralOrderedSubdivision bW (k + 1)).comp (integralOrderedMap (k + 1) f) := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedMap (k + 1) f
            (integralOrderedSubdivision b (k + 1) (Finsupp.single v 1)) =
          integralOrderedSubdivision bW (k + 1)
            (integralOrderedMap (k + 1) f (Finsupp.single v 1))
        rw [integralOrderedSubdivision_single_succ, integralOrderedMap_cone, ih,
          integralOrderedMap_boundary, integralOrderedMap_single,
          integralOrderedSubdivision_single_succ, hb]
      exact LinearMap.congr_fun h c

theorem integralOrderedPrism_map {W : Type v}
    (bW : ∀ n : Nat, (Fin (n + 1) → W) → W) (f : V → W)
    (hb : ∀ (n : Nat) (v : Fin (n + 1) → V), f (b n v) = bW n (f ∘ v))
    (k : Nat) (c : integralOrderedChains V k) :
    integralOrderedMap (k + 1) f (integralOrderedPrism b k c) =
      integralOrderedPrism bW k (integralOrderedMap k f c) := by
  induction k with
  | zero => simp only [integralOrderedPrism_zero, LinearMap.zero_apply, map_zero]
  | succ k ih =>
      have h : (integralOrderedMap (k + 2) f).comp (integralOrderedPrism b (k + 1)) =
          (integralOrderedPrism bW (k + 1)).comp (integralOrderedMap (k + 1) f) := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedMap (k + 2) f
            (integralOrderedPrism b (k + 1) (Finsupp.single v 1)) =
          integralOrderedPrism bW (k + 1)
            (integralOrderedMap (k + 1) f (Finsupp.single v 1))
        rw [integralOrderedPrism_single_succ, integralOrderedMap_cone,
          (integralOrderedMap (k + 1) f).map_sub,
          (integralOrderedMap (k + 1) f).map_sub,
          integralOrderedMap_single, integralOrderedSubdivision_map b bW f hb,
          ih, integralOrderedMap_boundary, integralOrderedMap_single,
          integralOrderedPrism_single_succ, hb]
      exact LinearMap.congr_fun h c

theorem integralOrderedSubdivision_support (A : Set V)
    (hA : ∀ (n : Nat) (v : Fin (n + 1) → V), Set.range v ⊆ A → b n v ∈ A)
    (k : Nat) (c : integralOrderedChains V k)
    (hc : ∀ v ∈ c.support, Set.range v ⊆ A) :
    ∀ v ∈ (integralOrderedSubdivision b k c).support, Set.range v ⊆ A := by
  classical
  induction k with
  | zero => exact hc
  | succ k ih =>
      have hfaces (v : Fin (k + 1) → V) (hv : Set.range v ⊆ A) :
          ∀ w ∈ (integralOrderedBoundary V k (Finsupp.single v 1)).support,
            Set.range w ⊆ A := by
        intro w hw
        rw [integralOrderedBoundary_single] at hw
        obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw)
        have heq : w = v ∘ i.succAbove :=
          ((Finsupp.mem_support_single _ _ _).mp (Finsupp.support_smul hwi)).1
        subst w
        rintro _ ⟨j, rfl⟩
        exact hv ⟨i.succAbove j, rfl⟩
      intro w hw
      change w ∈ (c.sum (fun v a => a • integralOrderedCone k (b k v)
        (integralOrderedSubdivision b k
          (integralOrderedBoundary V k (Finsupp.single v 1))))).support at hw
      obtain ⟨v, hvc, hw⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hw)
      have hwcone := Finsupp.support_smul hw
      change w ∈ (Finsupp.mapDomain
        (fun t : Fin k → V => Fin.cons (α := fun _ : Fin (k + 1) => V) (b k v) t)
        (integralOrderedSubdivision b k
          (integralOrderedBoundary V k (Finsupp.single v 1)))).support at hwcone
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hwcone)
      have htA : Set.range t ⊆ A :=
        ih _ (hfaces v (hc v hvc)) t ht
      rintro _ ⟨j, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hA k v (hc v hvc)
      · exact htA ⟨i, rfl⟩

theorem integralOrderedPrism_support (A : Set V)
    (hA : ∀ (n : Nat) (v : Fin (n + 1) → V), Set.range v ⊆ A → b n v ∈ A)
    (k : Nat) (c : integralOrderedChains V k)
    (hc : ∀ v ∈ c.support, Set.range v ⊆ A) :
    ∀ v ∈ (integralOrderedPrism b k c).support, Set.range v ⊆ A := by
  classical
  induction k with
  | zero =>
      intro v hv
      simp only [integralOrderedPrism_zero, LinearMap.zero_apply, Finsupp.support_zero,
        Finset.notMem_empty] at hv
  | succ k ih =>
      have hfaces (v : Fin (k + 1) → V) (hv : Set.range v ⊆ A) :
          ∀ w ∈ (integralOrderedBoundary V k (Finsupp.single v 1)).support,
            Set.range w ⊆ A := by
        intro w hw
        rw [integralOrderedBoundary_single] at hw
        obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw)
        have heq : w = v ∘ i.succAbove :=
          ((Finsupp.mem_support_single _ _ _).mp (Finsupp.support_smul hwi)).1
        subst w
        rintro _ ⟨j, rfl⟩
        exact hv ⟨i.succAbove j, rfl⟩
      intro w hw
      change w ∈ (c.sum (fun v a => a • integralOrderedCone (k + 1) (b k v)
        (Finsupp.single v 1 - integralOrderedSubdivision b (k + 1) (Finsupp.single v 1) -
          integralOrderedPrism b k
            (integralOrderedBoundary V k (Finsupp.single v 1))))).support at hw
      obtain ⟨v, hvc, hw⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hw)
      have hwcone := Finsupp.support_smul hw
      change w ∈ (Finsupp.mapDomain
        (fun t : Fin (k + 1) → V =>
          Fin.cons (α := fun _ : Fin (k + 2) => V) (b k v) t)
        (Finsupp.single v 1 - integralOrderedSubdivision b (k + 1) (Finsupp.single v 1) -
          integralOrderedPrism b k
            (integralOrderedBoundary V k (Finsupp.single v 1)))).support at hwcone
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hwcone)
      have hunit : ∀ z ∈ (Finsupp.single v (1 : Int)).support, Set.range z ⊆ A := by
        intro z hz
        have hzv : z = v := ((Finsupp.mem_support_single _ _ _).mp hz).1
        subst z
        exact hc v hvc
      have htA : Set.range t ⊆ A := by
        rcases Finset.mem_union.mp (Finsupp.support_sub ht) with hs | ht
        · rcases Finset.mem_union.mp (Finsupp.support_sub hs) with hv | hs
          · exact hunit t hv
          · exact integralOrderedSubdivision_support b A hA (k + 1) _ hunit t hs
        · exact ih _ (hfaces v (hc v hvc)) t ht
      rintro _ ⟨j, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hA k v (hc v hvc)
      · exact htA ⟨i, rfl⟩

end Poincare.Topology
