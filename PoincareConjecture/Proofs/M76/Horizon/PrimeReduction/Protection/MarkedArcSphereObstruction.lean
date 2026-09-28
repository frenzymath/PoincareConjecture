import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.LatticeSphereBall




set_option autoImplicit false
noncomputable section
open Set Metric Geometry

namespace PoincareConjecture.M76

variable {X : Type*} [TopologicalSpace X]

theorem preconnected_interior_or_exterior_of_frontier_avoidance
    {Q S : Set X} (hQ : IsClosed Q) (hS : IsPreconnected S)
    (havoid : Disjoint S (frontier Q)) :
    S ⊆ interior Q ∨ S ⊆ Qᶜ := by
  have hcover : S ⊆ interior Q ∪ Qᶜ := by
    intro x hx
    by_cases hi : x ∈ interior Q
    · exact Or.inl hi
    · refine Or.inr (fun hq => ?_)
      exact disjoint_left.mp havoid hx ⟨hQ.closure_eq.symm ▸ hq, hi⟩
  exact hS.subset_or_subset isOpen_interior hQ.isOpen_compl
    (disjoint_left.mpr (fun _ hi hc => hc (interior_subset hi))) hcover

theorem preconnected_meets_frontier_of_inside_outside
    {Q S : Set X} (hQ : IsClosed Q) (hS : IsPreconnected S)
    (hin : (S ∩ interior Q).Nonempty) (hout : (S \ Q).Nonempty) :
    (S ∩ frontier Q).Nonempty := by
  by_contra hn
  have hdis : Disjoint S (frontier Q) := disjoint_left.mpr (fun x hx hf => hn ⟨x, hx, hf⟩)
  rcases preconnected_interior_or_exterior_of_frontier_avoidance hQ hS hdis with h | h
  · obtain ⟨x, hx, hxQ⟩ := hout
    exact hxQ (interior_subset (h hx))
  · obtain ⟨x, hx, hxQ⟩ := hin
    exact h hx (interior_subset hxQ)



theorem single_contact_interval_avoids_interior
    {Q : Set X} (hQ : IsClosed Q) (gamma : ℝ → X)
    (hc : ContinuousOn gamma (Icc (0 : ℝ) 1))
    (hzero : gamma 0 ∉ Q) (hone : gamma 1 ∉ Q)
    (c : ℝ) (hcontact : ∀ t ∈ Icc (0 : ℝ) 1, gamma t ∈ frontier Q → t = c) :
    ∀ t ∈ Icc (0 : ℝ) 1, gamma t ∉ interior Q := by
  intro t ht hint
  by_cases htc : t ≤ c
  · have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 :=
      fun _ hu => ⟨hu.1, hu.2.trans ht.2⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, huf⟩ := preconnected_meets_frontier_of_inside_outside hQ
      ((convex_Icc (0 : ℝ) t).isPreconnected.image gamma (hc.mono hsub))
      ⟨gamma t, ⟨t, ⟨ht.1, le_rfl⟩, rfl⟩, hint⟩
      ⟨gamma 0, ⟨0, ⟨le_rfl, ht.1⟩, rfl⟩, hzero⟩
    have huc := hcontact u (hsub hu) huf
    have hut : u = t := le_antisymm hu.2 (by simpa only [huc] using htc)
    exact huf.2 (hut.symm ▸ hint)
  · have hsub : Icc t (1 : ℝ) ⊆ Icc (0 : ℝ) 1 :=
      fun _ hu => ⟨ht.1.trans hu.1, hu.2⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, huf⟩ := preconnected_meets_frontier_of_inside_outside hQ
      ((convex_Icc t (1 : ℝ)).isPreconnected.image gamma (hc.mono hsub))
      ⟨gamma t, ⟨t, ⟨le_rfl, ht.2⟩, rfl⟩, hint⟩
      ⟨gamma 1, ⟨1, ⟨ht.2, le_rfl⟩, rfl⟩, hone⟩
    exact htc ((hcontact u (hsub hu) huf) ▸ hu.1)



theorem two_sided_crossing_meets_interior
    {Q U : Set X} (hQ : IsClosed Q) (hreg : closure (interior Q) = Q)
    {p : X} (hp : p ∈ frontier Q) (hU : IsOpen U) (hpU : p ∈ U)
    (V : Bool → Set X) (hV : ∀ side, IsPreconnected (V side))
    (hsub : ∀ side, V side ⊆ U \ frontier Q)
    (hcover : U \ frontier Q ⊆ V false ∪ V true)
    (gamma : ℝ → X)
    (hcross : ∀ side, ∃ t ∈ Icc (0 : ℝ) 1, gamma t ∈ V side) :
    ∃ t ∈ Icc (0 : ℝ) 1, gamma t ∈ interior Q := by
  have hpin : p ∈ closure (interior Q) := hreg.symm ▸ hQ.frontier_subset hp
  obtain ⟨z, hzU, hzint⟩ := mem_closure_iff.mp hpin U hU hpU
  have hznot : z ∉ frontier Q := fun h => h.2 hzint
  have hside : ∃ side, z ∈ V side := by
    rcases hcover ⟨hzU, hznot⟩ with hz | hz
    · exact ⟨false, hz⟩
    · exact ⟨true, hz⟩
  obtain ⟨side, hzside⟩ := hside
  have havoid : Disjoint (V side) (frontier Q) :=
    disjoint_left.mpr (fun _ hx hf => (hsub side hx).2 hf)
  have hinside : V side ⊆ interior Q := by
    rcases preconnected_interior_or_exterior_of_frontier_avoidance hQ (hV side) havoid with h | h
    · exact h
    · exact (h hzside (interior_subset hzint)).elim
  obtain ⟨t, ht, htside⟩ := hcross side
  exact ⟨t, ht, hinside htside⟩

local notation "V3" => (Fin 3 → ℝ)




theorem ChartwisePLSphere.exists_lattice_ball_with_single_contact_arc_exclusion
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {S : Set (LatticeHandleAmbient ι κ L)} (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    ∃ Q : Set (LatticeHandleAmbient ι κ L), IsCompact Q ∧ frontier Q = S ∧
      IsUnitBallPair V3 Q S ∧ Q ⊆ interior (latticeHandleDomain ι κ L) ∧
      ∀ gamma : ℝ → LatticeHandleAmbient ι κ L,
        ContinuousOn gamma (Icc (0 : ℝ) 1) →
        gamma 0 ∈ frontier (latticeHandleDomain ι κ L) →
        gamma 1 ∈ frontier (latticeHandleDomain ι κ L) →
        ∀ c : ℝ, (∀ t ∈ Icc (0 : ℝ) 1, gamma t ∈ S → t = c) →
          ∀ t ∈ Icc (0 : ℝ) 1, gamma t ∉ interior Q := by
  obtain ⟨Q, hQ, hfront, hpair, hQR, _⟩ := s.exists_lattice_ball_pair_with_lift L he hdim hSR
  refine ⟨Q, hQ, hfront, hpair, hQR, ?_⟩
  intro gamma hc hzero hone c hcontact
  apply single_contact_interval_avoids_interior hQ.isClosed gamma hc
    (fun h => hzero.2 (hQR h)) (fun h => hone.2 (hQR h)) c
  intro t ht htf
  exact hcontact t ht (hfront ▸ htf)




theorem ChartwisePLSphere.no_single_two_sided_lattice_arc_crossing
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {S : Set (LatticeHandleAmbient ι κ L)} (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (gamma : ℝ → LatticeHandleAmbient ι κ L)
    (hc : ContinuousOn gamma (Icc (0 : ℝ) 1))
    (hzero : gamma 0 ∈ frontier (latticeHandleDomain ι κ L))
    (hone : gamma 1 ∈ frontier (latticeHandleDomain ι κ L))
    (c : ℝ) (hcontact : ∀ t ∈ Icc (0 : ℝ) 1, gamma t ∈ S → t = c)
    {p : LatticeHandleAmbient ι κ L} (hp : p ∈ S)
    (U : Set (LatticeHandleAmbient ι κ L)) (hU : IsOpen U) (hpU : p ∈ U)
    (V : Bool → Set (LatticeHandleAmbient ι κ L))
    (hV : ∀ side, IsPreconnected (V side)) (hsub : ∀ side, V side ⊆ U \ S)
    (hcover : U \ S ⊆ V false ∪ V true)
    (hcross : ∀ side, ∃ t ∈ Icc (0 : ℝ) 1, gamma t ∈ V side) : False := by
  obtain ⟨Q, hQ, hfront, hpair, _, havoid⟩ :=
    s.exists_lattice_ball_with_single_contact_arc_exclusion L he hdim hSR
  have hreg := (isConnected_interior_and_closure_of_unitBallPair hQ hfront hpair).2
  obtain ⟨t, ht, htQ⟩ := two_sided_crossing_meets_interior hQ.isClosed hreg
    (hfront.symm ▸ hp) hU hpU V hV (hfront.symm ▸ hsub) (hfront.symm ▸ hcover) gamma hcross
  exact havoid gamma hc hzero hone c hcontact t ht htQ




theorem ChartwisePLSphere.no_single_plane_chart_lattice_arc_crossing
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {S : Set (LatticeHandleAmbient ι κ L)} (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (gamma : ℝ → LatticeHandleAmbient ι κ L)
    (hc : ContinuousOn gamma (Icc (0 : ℝ) 1))
    (hzero : gamma 0 ∈ frontier (latticeHandleDomain ι κ L))
    (hone : gamma 1 ∈ frontier (latticeHandleDomain ι κ L))
    (c : ℝ) (hcontact : ∀ t ∈ Icc (0 : ℝ) 1, gamma t ∈ S → t = c)
    (T : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) ((ℝ × ℝ) × ℝ))
    (hplane : ∀ x ∈ T.source, x ∈ S ↔ (T x).2 = 0)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hball : ball (0 : (ℝ × ℝ) × ℝ) epsilon ⊆ T.target)
    (hcross : ∀ side : Bool, ∃ t ∈ Icc (0 : ℝ) 1,
      gamma t ∈ T.source ∧ T (gamma t) ∈ ball (0 : (ℝ × ℝ) × ℝ) epsilon ∧
        if side then 0 < (T (gamma t)).2 else (T (gamma t)).2 < 0) : False := by
  let half (side : Bool) : Set ((ℝ × ℝ) × ℝ) :=
    {z | if side then 0 < z.2 else z.2 < 0}
  let W (side) := ball (0 : (ℝ × ℝ) × ℝ) epsilon ∩ half side
  let U := T.symm '' ball (0 : (ℝ × ℝ) × ℝ) epsilon
  let V (side) := T.symm '' W side
  have hhalf (side) : Convex ℝ (half side) := by
    cases side
    · exact Convex.affine_preimage (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap (convex_Iio 0)
    · exact Convex.affine_preimage (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap (convex_Ioi 0)
  have hWtarget (side) : W side ⊆ T.target := fun _ hz => hball hz.1
  have hV (side) : IsPreconnected (V side) :=
    ((convex_ball _ _).inter (hhalf side)).isPreconnected.image T.symm
      (T.symm.continuousOn.mono (hWtarget side))
  have hU : IsOpen U := T.isOpen_image_symm_of_subset_target isOpen_ball hball
  have h0 : (0 : (ℝ × ℝ) × ℝ) ∈ T.target := hball (mem_ball_self hepsilon)
  have hpU : T.symm 0 ∈ U := ⟨0, mem_ball_self hepsilon, rfl⟩
  have hpS : T.symm 0 ∈ S := (hplane _ (T.map_target h0)).mpr (by rw [T.right_inv h0]; rfl)
  have hsub (side) : V side ⊆ U \ S := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
    intro hxS
    have hzero := (hplane _ (T.map_target (hWtarget side hz))).mp hxS
    rw [T.right_inv (hWtarget side hz)] at hzero
    have hsign := hz.2
    cases side
    · change z.2 < 0 at hsign
      exact (ne_of_lt hsign) hzero
    · change 0 < z.2 at hsign
      exact (ne_of_gt hsign) hzero
  have hcover : U \ S ⊆ V false ∪ V true := by
    rintro x ⟨⟨z, hz, rfl⟩, hxS⟩
    have hn : z.2 ≠ 0 := by
      intro heq
      apply hxS
      apply (hplane _ (T.map_target (hball hz))).mpr
      rwa [T.right_inv (hball hz)]
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact Or.inl ⟨z, ⟨hz, hneg⟩, rfl⟩
    · exact Or.inr ⟨z, ⟨hz, hpos⟩, rfl⟩
  have hcrossV (side) : ∃ t ∈ Icc (0 : ℝ) 1, gamma t ∈ V side := by
    obtain ⟨t, ht, hts, htb, hsign⟩ := hcross side
    exact ⟨t, ht, T (gamma t), ⟨htb, hsign⟩, T.left_inv hts⟩
  exact s.no_single_two_sided_lattice_arc_crossing L he hdim hSR gamma hc hzero hone
    c hcontact hpS U hU hpU V hV hsub hcover hcrossV

end PoincareConjecture.M76
