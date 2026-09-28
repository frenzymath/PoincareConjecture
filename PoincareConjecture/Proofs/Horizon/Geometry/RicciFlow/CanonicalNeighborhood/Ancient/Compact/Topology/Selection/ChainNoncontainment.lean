import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.NeckContainment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.InnerSlabCover
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Maximal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn.PositiveEnd
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.Certificate
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SphereContact
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Tails
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.CompactKappa

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

private theorem central_sphere_subset_of_inner_slab_contact
    (N P : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (hscale : P.scale ≤ (1.01 : ℝ) * N.scale)
    {x : M} (hxP : x ∈ P.central_sphere)
    (hx : x ∈ N.coordinate_map '' (univ ×ˢ
      Icc (-(3 / 4 : ℝ) * N.epsilon⁻¹) ((3 / 4 : ℝ) * N.epsilon⁻¹))) :
    P.central_sphere ⊆ N.carrier := by
  obtain ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ := hx
  have he := N.epsilon_pos
  have hs := N.scale_pos
  have hsP := P.scale_pos
  have hR := inv_pos.mpr he
  have ht' : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    constructor <;> linarith [ht.1, ht.2]
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    constructor <;> linarith
  have htabs : |t| ≤ (3 / 4 : ℝ) * N.epsilon⁻¹ :=
    abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hRlarge : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ he).mpr
    linarith
  have hroot : Real.sqrt (1 + N.epsilon) ≤ (1.01 : ℝ) := by
    have hh := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
  have hcentral : N.coordinate_map (q, 0) ∈ N.central_sphere := by
    rw [← N.centralSphere_range]
    exact mem_range_self q
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have haxis := N.edist_coordinate_map_axis_le q hzero ht'
  simp only [sub_zero] at haxis
  have haxisnum : N.scale * Real.sqrt (1 + N.epsilon) * |t| ≤
      (0.76 : ℝ) * N.scale * N.epsilon⁻¹ := by
    have hh := mul_le_mul
      (mul_le_mul_of_nonneg_left hroot hs.le) htabs (abs_nonneg t) (by positivity)
    nlinarith [mul_pos hs hR]
  have hcenter : g.edist N.center (N.coordinate_map (q, t)) ≤
      ENNReal.ofReal ((2 * Real.pi) * N.scale +
        (0.76 : ℝ) * N.scale * N.epsilon⁻¹) := by
    calc
      _ ≤ g.edist N.center (N.coordinate_map (q, 0)) +
          g.edist (N.coordinate_map (q, 0)) (N.coordinate_map (q, t)) :=
        Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal ((2 * Real.pi) * N.scale) +
          ENNReal.ofReal ((0.76 : ℝ) * N.scale * N.epsilon⁻¹) :=
        add_le_add (N.edist_central_sphere_le_two_pi_mul_scale
          N.center_on_central_sphere hcentral)
          (haxis.trans (ENNReal.ofReal_le_ofReal haxisnum))
      _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  intro y hy
  by_contra hout
  have hlower := N.balanced_edist_lower_of_not_mem_carrier hε hout
  have hupper : g.edist N.center y ≤
      ENNReal.ofReal ((2 * Real.pi) * N.scale +
        (0.76 : ℝ) * N.scale * N.epsilon⁻¹ + (2 * Real.pi) * P.scale) := by
    calc
      _ ≤ g.edist N.center (N.coordinate_map (q, t)) +
          g.edist (N.coordinate_map (q, t)) y := Manifold.riemannianEDist_triangle
      _ ≤ _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        exact add_le_add hcenter (P.edist_central_sphere_le_two_pi_mul_scale hxP hy)
  have hnum : (2 * Real.pi) * N.scale +
      (0.76 : ℝ) * N.scale * N.epsilon⁻¹ + (2 * Real.pi) * P.scale <
      (0.99 : ℝ) * N.scale * N.epsilon⁻¹ := by
    have h₁ := mul_le_mul_of_nonneg_right Real.pi_le_four hs.le
    have h₂ := mul_le_mul_of_nonneg_right Real.pi_le_four P.scale_pos.le
    have h₃ := mul_le_mul_of_nonneg_left hRlarge hs.le
    nlinarith
  exact (not_lt_of_ge (hlower.trans hupper))
    ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hnum)



theorem exists_contained_sphere_in_selected_neck_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (T : BalancedNeckChain g ε),
        ε ≤ ε₀ → T.HasQuarterCapture → ∀ a b : ℤ, T.shape = .finite a b →
        ∀ P : EpsilonNeck g, P.epsilon = ε →
        P.central_sphere ⊆ (T.unionOpen : Set M) →
        ∃ i ∈ T.shape.active, P.central_sphere ⊆ (T.neck i).carrier := by
  obtain ⟨ε₁, hε₁, _, hscale⟩ := EpsilonNeck.exists_scale_comparison_at_common_closure.{u}
  obtain ⟨ε₂, hε₂, _, hexclude⟩ := BalancedNeckChain.exists_positive_end_exclusion_threshold.{u}
  refine ⟨min ε₁ (min ε₂ (1 / 1000)), lt_min hε₁ (lt_min hε₂ (by norm_num)),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro M _ _ _ _ _ _ _ g ε T hε hcapture a b hshape P hP hsub
  have hsmall := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h₁ := hε.trans (min_le_left _ _)
  have h₂ := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  classical
  by_cases hmeet : ∃ i ∈ T.shape.active, ∃ x ∈ P.central_sphere,
      x ∈ (T.neck i).coordinate_map '' (univ ×ˢ
        Icc (-(3 / 4 : ℝ) * (T.neck i).epsilon⁻¹)
          ((3 / 4 : ℝ) * (T.neck i).epsilon⁻¹))
  · obtain ⟨i, hi, x, hxP, hx⟩ := hmeet
    have hiε := T.epsilon_eq i hi
    have hxN : x ∈ (T.neck i).carrier := by
      have hR := inv_pos.mpr (T.neck i).epsilon_pos
      apply (T.neck i).closedCollar_subset_carrier
        (r := (3 / 4 : ℝ) * (T.neck i).epsilon⁻¹) (by linarith)
      simpa only [EpsilonNeck.closedCollar, neg_mul] using hx
    have hs := (hscale (T.neck i) P (hiε.symm ▸ h₁) (hP.symm ▸ h₁)
      ⟨x, subset_closure hxN, subset_closure (P.central_sphere_subset hxP)⟩).2
    exact ⟨i, hi, central_sphere_subset_of_inner_slab_contact
      (T.neck i) P (hiε.symm ▸ hsmall) hs hxP hx⟩
  have hactive : T.shape.active = Icc a b := by rw [hshape]; rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := T.active_nonempty
    rw [hactive] at hi
    exact hi.1.trans hi.2
  have ha : a ∈ T.shape.active := hactive.symm ▸ ⟨le_rfl, hab⟩
  have hb : b ∈ T.shape.active := hactive.symm ▸ ⟨hab, le_rfl⟩
  let A := (T.neck a).region (-ε⁻¹) (-ε⁻¹ / 2)
  let B := (T.neck b).region (ε⁻¹ / 2) ε⁻¹
  have hcover : P.central_sphere ⊆ A ∪ B := by
    intro x hx
    obtain ⟨⟨i, hi⟩, hxi⟩ := mem_iUnion.mp (hsub hx)
    rcases T.mem_inner_slab_or_missing_neighbor_quarter hcapture hi hxi with
      ⟨j, hj, hxj⟩ | ⟨hprev, hxprev⟩ | ⟨hnext, hxnext⟩
    · exact (hmeet ⟨j, hj, x, hx, hxj⟩).elim
    · have heq : i = a := by rw [hactive] at hi hprev; simp only [mem_Icc] at *; omega
      exact Or.inl (by simpa only [A, heq] using hxprev)
    · have heq : i = b := by rw [hactive] at hi hnext; simp only [mem_Icc] at *; omega
      exact Or.inr (by simpa only [B, heq] using hxnext)
  have hdis : Disjoint A B := by
    rcases lt_or_eq_of_le hab with hlt | heq
    · exact (hexclude T h₂ a ha b hb hlt).mono_left
        ((T.neck a).region_subset_carrier _ _)
    · subst b
      apply disjoint_left.mpr
      intro x hx hy
      have he : 0 < ε := T.epsilon_eq a ha ▸ (T.neck a).epsilon_pos
      have hR := inv_pos.mpr he
      change x ∈ (T.neck a).region (-ε⁻¹) (-ε⁻¹ / 2) at hx
      change x ∈ (T.neck a).region (ε⁻¹ / 2) ε⁻¹ at hy
      linarith [hx.2.2, hy.2.1]
  rcases P.isConnected_central_sphere.isPreconnected.subset_or_subset
    ((T.neck a).isOpen_region _ _) ((T.neck b).isOpen_region _ _) hdis hcover with hA | hB
  · exact ⟨a, ha, hA.trans ((T.neck a).region_subset_carrier _ _)⟩
  · exact ⟨b, hb, hB.trans ((T.neck b).region_subset_carrier _ _)⟩

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
private theorem graph_transport_preserves_set (N : EpsilonNeck g)
    {U : Set M} (hNU : N.carrier ⊆ U)
    {r : ℝ} (hr : 0 < r) (hrN : r < N.epsilon⁻¹)
    (h : UnitTwoSphere → ℝ) (hh : Continuous h) (hbound : ∀ q, |h q| < r) :
    N.graphTransport hr hrN h hh hbound '' U = U := by
  let e := N.graphTransport hr hrN h hh hbound
  have hfix : EqOn e id Uᶜ := by
    intro x hx
    exact N.graphTransport_fixed hr hrN h hh hbound
      (fun hy => hx (hNU (N.closedCollar_subset_carrier hrN hy)))
  have hi := hfix.image_eq_self
  rw [e.image_compl] at hi
  exact compl_injective hi

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem transport_trans {U A B C : Set M} (e f : M ≃ₜ M)
    (heU : e '' U = U) (hfU : f '' U = U)
    (he : e '' A = B) (hf : f '' B = C) :
    (e.trans f) '' U = U ∧ (e.trans f) '' A = C := by
  constructor
  · change (f ∘ e) '' U = U
    rw [image_comp, heU, hfU]
  · change (f ∘ e) '' A = C
    rw [image_comp, he, hf]

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem transport_symm {U A B : Set M} (e : M ≃ₜ M)
    (heU : e '' U = U) (he : e '' A = B) :
    e.symm '' U = U ∧ e.symm '' B = A := by
  constructor
  · calc
      e.symm '' U = e.symm '' (e '' U) := congrArg (e.symm '' ·) heU.symm
      _ = U := e.toEquiv.symm_image_image U
  · rw [← he]
    exact e.toEquiv.symm_image_image A



theorem exists_selected_sphere_transport_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (T : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ i ∈ T.shape.active, ∀ j ∈ T.shape.active,
        ∃ e : M ≃ₜ M, e '' (T.unionOpen : Set M) = T.unionOpen ∧
          e '' (T.neck i).central_sphere = (T.neck j).central_sphere := by
  obtain ⟨ε₀, hε₀, hsmall, hgraph⟩ := EpsilonNeck.exists_sphereSlice_graph_and_isotopy.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε T hε
  have hsub (i : ℤ) (hi : i ∈ T.shape.active) :
      (T.neck i).carrier ⊆ (T.unionOpen : Set M) :=
    fun x hx => mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  have hadj (i : ℤ) (hi : i ∈ T.shape.active) (hj : i + 1 ∈ T.shape.active) :
      ∃ e : M ≃ₜ M, e '' (T.unionOpen : Set M) = T.unionOpen ∧
        e '' (T.neck i).central_sphere = (T.neck (i + 1)).central_sphere := by
    let A := T.neck i
    let B := T.neck (i + 1)
    have hA : A.epsilon = ε := T.epsilon_eq i hi
    have hB : B.epsilon = ε := T.epsilon_eq (i + 1) hj
    let s := -(3 / 4 : ℝ) * B.epsilon⁻¹
    have hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by
      dsimp [s]; constructor <;> linarith [inv_pos.mpr B.epsilon_pos]
    have hcontained (q : UnitTwoSphere) : B.coordinate_map (q, s) ∈ A.carrier := by
      apply (T.overlap_contains_quarters i hi hj).2
      refine ⟨B.coordinate_map_mem ⟨mem_univ _, hs⟩, ?_⟩
      rw [B.coordinate_inverse_coordinate_map ⟨mem_univ _, hs⟩, ← hB]
      dsimp [s]
      constructor <;> linarith [inv_pos.mpr B.epsilon_pos]
    obtain ⟨h, hh, hdom, heq, _⟩ := hgraph A B (hA.symm ▸ hε) (hB.symm ▸ hε)
      hs hcontained
    obtain ⟨r, hr, hrA, hbound⟩ := A.exists_graph_collar h hh.continuous hdom
    obtain ⟨t, ht, htB, htbound⟩ := B.exists_graph_collar (fun _ => s)
      continuous_const (fun _ => hs)
    let e := A.graphTransport hr hrA h hh.continuous hbound
    let f := B.graphTransport ht htB (fun _ => s) continuous_const htbound
    have heU : e '' (T.unionOpen : Set M) = T.unionOpen :=
      graph_transport_preserves_set A (hsub i hi) hr hrA h hh.continuous hbound
    have hfU : f '' (T.unionOpen : Set M) = T.unionOpen :=
      graph_transport_preserves_set B (hsub (i + 1) hj) ht htB
        (fun _ => s) continuous_const htbound
    have heS : e '' A.central_sphere = range (fun q => B.coordinate_map (q, s)) :=
      (A.graphTransport_image_central_sphere hr hrA h hh.continuous hbound).trans heq.symm
    have hfS : f '' B.central_sphere = range (fun q => B.coordinate_map (q, s)) :=
      B.graphTransport_image_central_sphere ht htB (fun _ => s) continuous_const htbound
    have hfi := transport_symm f hfU hfS
    exact ⟨e.trans f.symm, transport_trans e f.symm heU hfi.1 heS hfi.2⟩
  have hle (i j : ℤ) (hi : i ∈ T.shape.active) (hj : j ∈ T.shape.active) (hij : i ≤ j) :
      ∃ e : M ≃ₜ M, e '' (T.unionOpen : Set M) = T.unionOpen ∧
        e '' (T.neck i).central_sphere = (T.neck j).central_sphere := by
    have hn : ∀ n : ℕ, i + (n : ℤ) ∈ T.shape.active →
        ∃ e : M ≃ₜ M, e '' (T.unionOpen : Set M) = T.unionOpen ∧
          e '' (T.neck i).central_sphere = (T.neck (i + (n : ℤ))).central_sphere := by
      intro n
      induction n with
      | zero =>
        intro _
        exact ⟨Homeomorph.refl M, by simp, by simp⟩
      | succ n ih =>
        intro hn
        have hmid : i + (n : ℤ) ∈ T.shape.active :=
          T.shape.ordConnected_active.out hi hn ⟨by omega, by omega⟩
        have hnext : i + (n : ℤ) + 1 ∈ T.shape.active := by simpa [add_assoc] using hn
        obtain ⟨e, heU, he⟩ := ih hmid
        obtain ⟨f, hfU, hf⟩ := hadj (i + (n : ℤ)) hmid hnext
        exact ⟨e.trans f, (transport_trans e f heU hfU he hf).1,
          by simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
            (transport_trans e f heU hfU he hf).2⟩
    have heq : i + ((j - i).toNat : ℤ) = j := by omega
    simpa only [heq] using hn (j - i).toNat (heq.symm ▸ hj)
  intro i hi j hj
  rcases le_total i j with hij | hji
  · exact hle i j hi hj hij
  · obtain ⟨e, heU, he⟩ := hle j i hj hi hji
    exact ⟨e.symm, transport_symm e heU he⟩

omit [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] in
private theorem not_isCompact_of_frontier_eq_cylinder_middle
    {U K : Set M} (W : OpenCylinderModel U) (hKU : K ⊆ U)
    (hfront : frontier K = W.middleSphere) (hint : (interior K).Nonempty) :
    ¬ IsCompact K := by
  intro hK
  have hhalf : (1 / 2 : ℝ) ∈ Ioo 0 1 := by constructor <;> norm_num
  have hmiddle {x : M} (hx : x ∈ W.middleSphere) : (W.inverse x).2 = 1 / 2 := by
    obtain ⟨z, ⟨_, hz⟩, rfl⟩ := hx
    have hz' : z.2 = 1 / 2 := hz
    rw [W.left_inverse ⟨mem_univ _, hz'.symm ▸ hhalf⟩, hz']
  have havoid (side : Bool) : Disjoint (W.tail side (1 / 2)) (frontier K) := by
    rw [hfront]
    apply disjoint_left.mpr
    intro x hx hxm
    have ht := ((W.mem_tail_iff side hhalf).mp hx).2
    rw [hmiddle hxm] at ht
    cases side <;> exact lt_irrefl _ ht
  have hfill (side : Bool) {x : M} (hx : x ∈ W.tail side (1 / 2))
      (hxK : x ∈ interior K) : W.tail side (1 / 2) ⊆ K :=
    (Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      (W.isConnected_tail side hhalf).isPreconnected (havoid side)
      ⟨x, hx, hxK⟩).trans interior_subset
  obtain ⟨r, hr, hnegative, hpositive, _, _⟩ := W.exists_tails_disjoint_of_isCompact hK hKU
  have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1, by linarith [hr.2]⟩
  have hrc : 1 - r ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hr.1, hr.2]
  obtain ⟨x, hx⟩ := hint
  have hxU := hKU (interior_subset hx)
  have hne : (W.inverse x).2 ≠ 1 / 2 := by
    intro heq
    have hxm : x ∈ W.middleSphere :=
      ⟨W.inverse x, ⟨mem_univ _, heq⟩, W.right_inverse hxU⟩
    exact (hfront.symm ▸ hxm).2 hx
  rcases lt_or_gt_of_ne hne with hlo | hhi
  · have hsub := hfill false ((W.mem_tail_iff false hhalf).mpr ⟨hxU, hlo⟩) hx
    obtain ⟨y, hy⟩ := (W.isConnected_tail false hr01).nonempty
    have hy' := (W.mem_tail_iff false hr01).mp hy
    exact disjoint_left.mp hnegative hy
      (hsub ((W.mem_tail_iff false hhalf).mpr ⟨hy'.1, hy'.2.trans hr.2⟩))
  · have hsub := hfill true ((W.mem_tail_iff true hhalf).mpr ⟨hxU, hhi⟩) hx
    obtain ⟨y, hy⟩ := (W.isConnected_tail true hrc).nonempty
    have hy' := (W.mem_tail_iff true hrc).mp hy
    have hylt : 1 - r < (W.inverse y).2 := by simpa using hy'.2
    exact disjoint_left.mp hpositive hy
      (hsub ((W.mem_tail_iff true hhalf).mpr ⟨hy'.1, by dsimp; linarith [hr.2]⟩))



theorem exists_selected_sphere_compact_filling_obstruction_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (T : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ a b : ℤ, T.shape = .finite a b →
        ∀ i ∈ T.shape.active, ∀ K : Set M, K ⊆ (T.unionOpen : Set M) →
        frontier K = (T.neck i).central_sphere → (interior K).Nonempty → ¬ IsCompact K := by
  obtain ⟨ε₁, hε₁, hsmall, hfinite⟩ :=
    BalancedNeckChain.exists_finite_cylinder_with_middle_threshold.{u}
  obtain ⟨ε₂, hε₂, _, htransport⟩ := exists_selected_sphere_transport_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε T hε a b hshape i hi K hKU hfront hint hK
  obtain ⟨D, j, hj, c, hc, hDzero⟩ := hfinite T (hε.trans (min_le_left _ _)) a b hshape
  obtain ⟨E, hEzero⟩ := (T.neck j).exists_unit_to_real_cylinder
  let q₀ := ((T.neck j).coordinate_inverse (T.neck j).center).1
  let W : OpenCylinderModel (T.unionOpen : Set M) :=
    OpenCylinderModel.ofDiffeomorph T.unionOpen (E.trans D) q₀
  have hmiddle : W.middleSphere =
      range (fun q : UnitTwoSphere => (T.neck j).coordinate_map (q, c)) := by
    dsimp only [W]
    rw [OpenCylinderModel.ofDiffeomorph_middleSphere, ← hDzero]
    congr 1
    funext q
    change (D (E ⟨(q, 1 / 2), mem_univ _, by norm_num⟩) : M) = _
    rw [hEzero q]
  obtain ⟨e, heU, he⟩ := htransport T (hε.trans (min_le_right _ _)) i hi j hj
  have hc' : c ∈ Ioo (-(T.neck j).epsilon⁻¹) (T.neck j).epsilon⁻¹ := by
    simpa only [T.epsilon_eq j hj] using hc
  obtain ⟨r, hr, hrN, hbound⟩ := (T.neck j).exists_graph_collar
    (fun _ => c) continuous_const (fun _ => hc')
  let f := (T.neck j).graphTransport hr hrN (fun _ => c) continuous_const hbound
  have hfU : f '' (T.unionOpen : Set M) = T.unionOpen :=
    graph_transport_preserves_set (T.neck j)
      (fun x hx => mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩)
      hr hrN (fun _ => c) continuous_const hbound
  have hf : f '' (T.neck j).central_sphere = W.middleSphere :=
    ((T.neck j).graphTransport_image_central_sphere hr hrN
      (fun _ => c) continuous_const hbound).trans hmiddle.symm
  let k := e.trans f
  have hk := transport_trans e f heU hfU he hf
  apply not_isCompact_of_frontier_eq_cylinder_middle W
    ((image_mono hKU).trans hk.1.subset)
  · rw [← k.image_frontier, hfront]
    exact hk.2
  · rw [← k.image_interior]
    exact hint.image k
  · exact hK.image k.continuous



theorem exists_closed_core_chain_noncontainment_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (T : BalancedNeckChain g ε),
        ε ≤ ε₀ → T.HasQuarterCapture → ∀ a b : ℤ, T.shape = .finite a b →
        ∀ C : CapCertificate g, C.epsilon = ε → ¬ C.closed_core ⊆ (T.unionOpen : Set M) := by
  obtain ⟨ε₁, hε₁, hsmall, hsphere⟩ := exists_contained_sphere_in_selected_neck_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hfilling⟩ := exists_selected_sphere_compact_filling_obstruction_threshold.{u}
  obtain ⟨ε₃, hε₃, _, htransport⟩ := EpsilonNeck.exists_contained_compact_transport.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε T hε hcapture a b hshape C hC hsub
  have hboundary : C.boundary_neck.central_sphere ⊆ (T.unionOpen : Set M) := by
    rw [← C.boundary_eq_neck_sphere]
    exact C.boundary_subset_closed_core.trans hsub
  obtain ⟨i, hi, hiC⟩ := hsphere T (hε.trans (min_le_left _ _)) hcapture a b hshape
    C.boundary_neck (C.boundary_neck_epsilon.trans hC) hboundary
  have hpos : 0 < ε := hC ▸ C.epsilon_pos
  obtain ⟨e, L, _, hL, hfix, _, he⟩ := htransport hpos
    (hε.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (T.neck i) C.boundary_neck (T.epsilon_eq i hi)
    (C.boundary_neck_epsilon.trans hC) hiC
  have hcore : e.symm '' C.closed_core ⊆ (T.unionOpen : Set M) := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hout
    have h := hfix (e.symm x)
      (fun hy => hout (mem_iUnion.mpr ⟨⟨i, hi⟩, hL hy⟩))
    rw [e.apply_symm_apply] at h
    exact hout (h ▸ hsub hx)
  have hfront : frontier (e.symm '' C.closed_core) = (T.neck i).central_sphere := by
    rw [← e.symm.image_frontier, C.core_frontier_eq_boundary,
      C.boundary_eq_neck_sphere, ← he]
    exact e.toEquiv.symm_image_image (T.neck i).central_sphere
  have hint : (interior (e.symm '' C.closed_core)).Nonempty := by
    rw [← e.symm.image_interior, ← C.core_eq_interior_closed_core]
    exact C.core_nonempty.image e.symm
  exact hfilling T (hε.trans ((min_le_right _ _).trans (min_le_left _ _)))
    a b hshape i hi (e.symm '' C.closed_core) hcore hfront hint
    (C.closed_core_compact.image e.symm.continuous)

end PoincareConjecture.CompactKappa
