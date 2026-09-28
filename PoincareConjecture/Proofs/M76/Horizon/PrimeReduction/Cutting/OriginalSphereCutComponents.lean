import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalFinitePLSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedComponentDomains
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSphereTopology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.FiniteCollarProduct









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_sphere_cut_components
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ (Q : Set X) (B : κ × Bool → Set X) (H : ∀ b, S b.1 ≃ₜ B b)
      (_sB : ∀ b, ChartwisePLSphere e (B b)) (O : κ → Set X)
      (D : ConnectedComponents Q → Set X) (owner : κ × Bool → ConnectedComponents Q),
      Finite (ConnectedComponents Q) ∧
      Q = R \ ⋃ i, O i ∧ IsCompact Q ∧ PLDomain e Q ∧
      (∀ i, IsOpen (O i) ∧ IsCompact (closure (O i)) ∧
        IsConnected (closure (O i)) ∧ closure (O i) ⊆ U ∩ interior R) ∧
      Pairwise (fun i j => Disjoint (closure (O i)) (closure (O j))) ∧
      (∀ i, closure (O i) ∩ Q = B (i, false) ∪ B (i, true)) ∧
      (⋃ i, closure (O i)) ∪ Q = R ∧ Q \ U = R \ U ∧
      Pairwise (fun b d => Disjoint (B b) (B d)) ∧
      (∀ c, IsCompact (D c) ∧ PLDomain e (D c) ∧ IsConnected (D c) ∧ D c ⊆ Q ∧
        frontier (D c) = (D c ∩ frontier R) ∪ ⋃ b ∈ {b | owner b = c}, B b) ∧
      Pairwise (fun c d => Disjoint (D c) (D d)) ∧ (⋃ c, D c) = Q ∧
      (∀ b c, B b ⊆ D c ↔ owner b = c) ∧
      (∀ b c, owner b ≠ c → Disjoint (B b) (D c)) ∧
      (∀ x : Q, D (ConnectedComponents.mk x) = connectedComponentIn Q x) ∧
      (∀ i d, closure (O i) ∩ D d =
        ⋃ b ∈ {b : Bool | owner (i, b) = d}, B (i, b)) ∧
      ∃ W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i),
        (∀ i x, (W i (x, 0) : X) = H (i, false) x ∧
          (W i (x, 1) : X) = H (i, true) x) ∧
        (∀ i x, (W i (x, ⟨(1 / 2 : ℝ), by norm_num⟩) : X) = x) := by
  classical
  obtain ⟨t, N, HB, c, ε, Q, B, H, sB, hpiece, hclosedDis, _, hHval, hBdis,
    _, hQeq, hQ, hQPL, _, hQf, hCQ, _, hcover, _, _, houtside, _⟩ :=
    exists_original_finite_pl_sphere_cut S sS hdis hR he hSR hU hSU
  let O : κ → Set X := fun i => c i '' ((N i).space ×ˢ Ioo (-ε i) (ε i))
  have hclosure (i : κ) :
      closure (O i) = c i '' ((N i).space ×ˢ Icc (-ε i) (ε i)) :=
    (hpiece i).2.2.2.2.2.2.2.2.1
  have hBfront (b : κ × Bool) : B b ⊆ frontier Q := by
    rw [hQf]
    exact fun _ hx => Or.inr (mem_iUnion.mpr ⟨b, hx⟩)
  have hsphereconn {T : Set X} (s : ChartwisePLSphere e T) : IsConnected T := by
    let f := s.parametrization.symm.trans
      (Homeomorph.setCongr (frontier_closedBall (0 : V3) one_ne_zero).symm)
    exact f.isConnected_of_convex_frontier (isCompact_closedBall _ _)
      (convex_closedBall _ _) ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
      (by simp)
  obtain ⟨hfinite, D, owner, hD, hDdis, hDcover, howner, havoid, hactual⟩ :=
    exists_marked_pl_component_domains hQ hQPL B (fun b => hsphereconn (sB b)) hBfront
  refine ⟨Q, B, H, sB, O, D, owner, hfinite, hQeq, hQ, hQPL, ?_, ?_, ?_, ?_,
    houtside, hBdis, ?_, hDdis, hDcover, howner, havoid, hactual, ?_, ?_⟩
  · intro i
    obtain ⟨_, hPL, _, _, hε, hεle, ho, hc, _, hi⟩ := hpiece i
    have hN : IsConnected (N i).space := isConnected_iff_connectedSpace.mpr
      ((HB i).connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp (hsphereconn (sS i))))
    have hprod := hN.prod (isConnected_Icc (show -ε i ≤ ε i by linarith))
    have hconn : IsConnected (closure (O i)) := by
      rw [hclosure]
      apply hprod.image
      apply hPL.continuousOn.mono
      rintro ⟨x, r⟩ ⟨hx, hr⟩
      exact ⟨hx, by constructor <;> linarith [hr.1, hr.2]⟩
    exact ⟨ho, (hclosure i).symm ▸ hc, hconn, (hclosure i).symm ▸ hi⟩
  · intro i j hij
    simpa only [hclosure] using hclosedDis hij
  · intro i
    simpa only [hclosure] using hCQ i
  · simpa only [hclosure] using hcover
  · intro d
    refine ⟨(hD d).1, (hD d).2.1, (hD d).2.2.1, (hD d).2.2.2.1, ?_⟩
    rw [(hD d).2.2.2.2, hQf, inter_union_distrib_left]
    congr 1
    ext x
    constructor
    · rintro ⟨hxD, hxB⟩
      obtain ⟨b, hb⟩ := mem_iUnion.mp hxB
      have hbd : owner b = d := by
        by_contra h
        exact disjoint_left.mp (havoid b d h) hb hxD
      exact mem_iUnion₂.mpr ⟨b, hbd, hb⟩
    · intro hx
      obtain ⟨b, hbd, hb⟩ := mem_iUnion₂.mp hx
      exact ⟨(howner b d).mpr hbd hb, mem_iUnion.mpr ⟨b, hb⟩⟩
  · intro i d
    have hi : closure (O i) ∩ Q = B (i, false) ∪ B (i, true) := by
      simpa only [hclosure] using hCQ i
    ext x
    constructor
    · rintro ⟨hxC, hxD⟩
      have hxB := hi.subset ⟨hxC, (hD d).2.2.2.1 hxD⟩
      have hb : ∃ b : Bool, x ∈ B (i, b) := by
        rcases hxB with hb | hb
        · exact ⟨false, hb⟩
        · exact ⟨true, hb⟩
      obtain ⟨b, hb⟩ := hb
      have hbd : owner (i, b) = d := by
        by_contra h
        exact disjoint_left.mp (havoid (i, b) d h) hb hxD
      exact mem_iUnion₂.mpr ⟨b, hbd, hb⟩
    · intro hx
      obtain ⟨b, hbd, hb⟩ := mem_iUnion₂.mp hx
      refine ⟨?_, (howner (i, b) d).mpr hbd hb⟩
      apply (hi.symm.subset _).1
      cases b
      · exact Or.inl hb
      · exact Or.inr hb
  · have hprod (i : κ) :
        ∃ W : (S i × unitInterval) ≃ₜ closure (O i),
          (∀ x, (W (x, 0) : X) = H (i, false) x ∧
            (W (x, 1) : X) = H (i, true) x) ∧
          (∀ x, (W (x, ⟨(1 / 2 : ℝ), by norm_num⟩) : X) = x) := by
      obtain ⟨hN, hPL, hinj, hcenter, hε, hεle, _⟩ := hpiece i
      have hi : InjOn (c i) ((N i).space ×ˢ Icc (-1 : ℝ) 1) := by
        intro x hx y hy hxy
        exact congrArg Subtype.val (hinj.injective
          (show (c i) (⟨x, hx⟩ : ((N i).space ×ˢ Icc (-1 : ℝ) 1 : Set _)) =
            (c i) (⟨y, hy⟩ : ((N i).space ×ˢ Icc (-1 : ℝ) 1 : Set _)) from hxy))
      obtain ⟨W₀, hW₀⟩ := exists_closed_collar_product
        ((N i).isCompact_space_of_finite hN) (c i) hPL.continuousOn hi hε
        (show ε i ≤ 1 by linarith)
      let W : (S i × unitInterval) ≃ₜ closure (O i) :=
        (((HB i).symm.prodCongr (Homeomorph.refl unitInterval)).trans W₀).trans
          (Homeomorph.setCongr (hclosure i).symm)
      have hval (z : S i × unitInterval) :
          (W z : X) = c i (((HB i).symm z.1 : t i → ℝ × V3),
            (2 * (z.2 : ℝ) - 1) * ε i) := hW₀ _
      refine ⟨W, ?_, ?_⟩
      · intro x
        constructor <;> rw [hval, hHval] <;> norm_num
      · intro x
        rw [hval]
        norm_num only [zero_mul]
        rw [hcenter]
        exact congrArg Subtype.val ((HB i).apply_symm_apply x)
    choose W hW hcenter using hprod
    exact ⟨W, hW, hcenter⟩

end PoincareConjecture.M76
