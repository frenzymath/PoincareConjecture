import PoincareConjecture.Proofs.M76.Mathlib.CompactAffineImageLiftFactorization
import PoincareConjecture.Proofs.M76.Mathlib.LocallyInjectiveConvexOverlap

set_option autoImplicit false

universe w

open Set Topology

namespace Geometry

theorem exists_finite_marks_for_affine_cell_lifts
    {U V ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
    (D : Set U) (C : ι → Set U) (hcompact : ∀ i, IsCompact (C i))
    (hconvex : ∀ i, Convex ℝ (C i)) (hcover : D = ⋃ i, C i)
    (F : U → V) (A : ι → U →ᴬ[ℝ] V) (hF : ∀ i, EqOn F (A i) (C i)) :
    ∃ S : Set D, S.Finite ∧
      ∀ (E : Type w) [TopologicalSpace E] [T2Space E]
        (p : E → V), IsLocallyInjective p →
        ∀ (g : C(D, E)), (∀ u, p (g u) = F u) →
        ∀ (T : E ≃ₜ E), (∀ e, p (T e) = p e) → (∀ e, T e ≠ e) →
        (range g ∩ T '' range g).Nonempty →
        ∃ a ∈ S, ∃ b ∈ S, g a = T (g b) ∧ g a ≠ g b := by
  classical
  have hCD (i : ι) : C i ⊆ D := by
    intro x hx
    rw [hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩
  let J := {ij : ι × ι // (A ij.1 '' C ij.1 ∩ A ij.2 '' C ij.2).Nonempty}
  have hchoose (j : J) : ∃ u v : D,
      (u : U) ∈ C j.val.1 ∧ (v : U) ∈ C j.val.2 ∧ A j.val.1 u = A j.val.2 v := by
    obtain ⟨x, ⟨u, hu, hux⟩, v, hv, hvx⟩ := j.property
    exact ⟨⟨u, hCD _ hu⟩, ⟨v, hCD _ hv⟩, hu, hv, hux.trans hvx.symm⟩
  choose sampleA sampleB hsample using hchoose
  let S : Set D := range sampleA ∪ range sampleB
  refine ⟨S, (finite_range sampleA).union (finite_range sampleB), ?_⟩
  intro E instE instT2 p hp g hg T hTp hTne hmeet
  let gi (i : ι) : C(C i, E) :=
    ⟨fun u => g ⟨u, hCD i u.property⟩,
      g.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have hfactor (i : ι) : ∃ k : C(A i '' C i, E),
      (∀ v, p (k v) = (v : V)) ∧
      (∀ u : C i, k ⟨A i u, ⟨u, u.property, rfl⟩⟩ = gi i u) ∧ range k = range (gi i) :=
    hp.exists_compact_affine_image_factorization (hcompact i) (hconvex i) (A i) (gi i)
      (fun u => (hg ⟨u, hCD i u.property⟩).trans (hF i u.property))
  choose k hk using hfactor
  have hkvalue (i : ι) (u : D) (hu : (u : U) ∈ C i) :
      k i ⟨A i u, ⟨u, hu, rfl⟩⟩ = g u := (hk i).2.1 ⟨u, hu⟩
  obtain ⟨z, ⟨x, hxz⟩, y, ⟨y0, hy0⟩, hyz⟩ := hmeet
  have hxy : g x = T (g y0) := hxz.trans (hyz.symm.trans (congrArg T hy0).symm)
  have hxD : (x : U) ∈ ⋃ i, C i := hcover.subset x.property
  have hyD : (y0 : U) ∈ ⋃ i, C i := hcover.subset y0.property
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
  obtain ⟨j, hyj⟩ := mem_iUnion.mp hyD
  let xi : A i '' C i := ⟨A i x, ⟨x, hxi, rfl⟩⟩
  let yj : A j '' C j := ⟨A j y0, ⟨y0, hyj, rfl⟩⟩
  have hkxi : k i xi = g x := hkvalue i x hxi
  have hkyj : k j yj = g y0 := hkvalue j y0 hyj
  let Tkj : C(A j '' C j, E) :=
    ⟨fun v => T (k j v), T.continuous.comp (k j).continuous⟩
  have hkmeet : (range (k i) ∩ range Tkj).Nonempty :=
    ⟨g x, ⟨xi, hkxi⟩, ⟨yj, (congrArg T hkyj).trans hxy.symm⟩⟩
  obtain ⟨hagree, hrange⟩ := hp.convex_cell_overlap
    (Convex.affine_image (A i).toAffineMap (hconvex i))
    (Convex.affine_image (A j).toAffineMap (hconvex j))
    (k i) Tkj (hk i).1 (fun v => (hTp (k j v)).trans ((hk j).1 v)) hkmeet
  obtain ⟨e, he⟩ := hkmeet
  rw [hrange] at he
  obtain ⟨common, _⟩ := he
  let pair : J := ⟨(i, j), ⟨common, common.property⟩⟩
  let a : D := sampleA pair
  let b : D := sampleB pair
  have ha : (a : U) ∈ C i := (hsample pair).1
  have hb : (b : U) ∈ C j := (hsample pair).2.1
  have habcoord : A i a = A j b := (hsample pair).2.2
  let av : A i '' C i := ⟨A i a, ⟨a, ha, rfl⟩⟩
  let bv : A j '' C j := ⟨A j b, ⟨b, hb, rfl⟩⟩
  have havj : A i a ∈ A j '' C j := ⟨b, hb, habcoord.symm⟩
  let c : (A i '' C i ∩ A j '' C j : Set V) := ⟨A i a, av.property, havj⟩
  have hcommon := hagree c
  change k i av = T (k j ⟨A i a, havj⟩) at hcommon
  have heqv : (⟨A i a, havj⟩ : A j '' C j) = bv := Subtype.ext habcoord
  rw [heqv] at hcommon
  have hab : g a = T (g b) := (hkvalue i a ha).symm.trans
    (hcommon.trans (congrArg T (hkvalue j b hb)))
  refine ⟨a, Or.inl ⟨pair, rfl⟩, b, Or.inr ⟨pair, rfl⟩, hab, ?_⟩
  exact fun heq => hTne (g b) (hab.symm.trans heq)

end Geometry
