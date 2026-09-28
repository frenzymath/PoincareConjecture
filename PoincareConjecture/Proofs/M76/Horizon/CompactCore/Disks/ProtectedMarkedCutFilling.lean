import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.EssentialProtectedFilling
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.ProtectedCutFilling
import PoincareConjecture.Proofs.M76.Dehn.MarkedSquarePLApproximation











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1



theorem PLDomain.exists_protected_marked_cut_filling
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K Y F : Set X}
    (hK : PLDomain e K) (hY : IsOpen Y) (hcut : Y ∩ frontier K = F)
    (f : C(D, Y)) (rim : C(Q, F))
    (hrim : ∀ u : Q, (f ⟨u, sphere_subset_closedBall u.property⟩ : X) = (rim u : X))
    (hproper : ∀ x : D, (f x : X) ∈ F ↔ (x : V2) ∈ Q)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1) :
    ∃ (d : ι × Y → OpenPartialHomeomorph Y V3) (P : Set Y),
      PLDomain d P ∧
      (P = (Subtype.val : Y → X) ⁻¹' K ∨
        P = (Subtype.val : Y → X) ⁻¹' (interior K)ᶜ) ∧
      frontier P = (Subtype.val : Y → X) ⁻¹' F ∧
      (∀ k, MapsTo (Subtype.val : Y → X) (d k).source (e k.1).source) ∧
      (∀ k, (d k : Y → V3) = (e k.1) ∘ Subtype.val) ∧
      ∃ (g : V2 → Y) (gamma : C(Q, ((Subtype.val : Y → X) ⁻¹' F))),
        PolyhedralPLInCharts d g D ∧ MapsTo g D P ∧
        (∀ u : Q, g u = (gamma u : Y)) ∧
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 := by
  classical
  let x0 : D := ⟨0, mem_closedBall_self zero_le_one⟩
  let g0 : V2 → X := fun x => if hx : x ∈ D then (f ⟨x, hx⟩ : X) else (f x0 : X)
  have hg0 (x : D) : g0 x = (f x : X) := by simp only [g0, dif_pos x.property]
  have hcontinuous : ContinuousOn g0 D := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hfun : Set.domRestrict D g0 = fun x : D => (f x : X) := funext hg0
    rw [hfun]
    exact continuous_subtype_val.comp f.continuous
  have hgY : MapsTo g0 D Y := by
    intro x hx
    rw [hg0 ⟨x, hx⟩]
    exact (f ⟨x, hx⟩).property
  have hproper0 (x : D) : g0 x ∈ F ↔ (x : V2) ∈ Q := by
    rw [hg0]
    exact hproper x
  have hrim0 (u : Q) : g0 u = (rim u : X) :=
    (hg0 ⟨u, sphere_subset_closedBall u.property⟩).trans (hrim u)
  obtain ⟨d, P, hP, hside, hfront, hsource, hval, cutFill, cutRim,
    _, _, hpair, _, hout⟩ := hK.exists_protected_cut_filling hY hcut
      hcontinuous hgY hproper0 rim hrim0 hessential
  have hmark : (Subtype.val : Y → X) ⁻¹' F ⊆ frontier P := hfront.symm.subset
  have hmarkopen : IsOpen ((Subtype.val : frontier P → Y) ⁻¹'
      ((Subtype.val : Y → X) ⁻¹' F)) := by
    have heq : (Subtype.val : frontier P → Y) ⁻¹'
        ((Subtype.val : Y → X) ⁻¹' F) = univ := by
      ext x
      simp only [mem_preimage, mem_univ, iff_true]
      exact hfront.subset x.property
    rw [heq]
    exact isOpen_univ
  have hexcluded : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map cutRim.continuous)) ∉
      (⊥ : Subgroup (FundamentalGroup ((Subtype.val : Y → X) ⁻¹' F)
        (cutRim Dehn.squareRimBase))) := fun h => hout (Subgroup.mem_bot.mp h)
  obtain ⟨g, gamma, hg, hgP, hgamma, H, houtside⟩ :=
    Dehn.exists_marked_PL_square_pair hP _ hmark hmarkopen cutFill cutRim hpair ⊥ hexcluded
  refine ⟨d, P, hP, hside, hfront, hsource, hval, g, gamma, hg, hgP, hgamma, ?_⟩
  intro htrivial
  apply houtside
  apply Subgroup.mem_bot.mpr
  exact ((H.evalAt Dehn.squareRimBase).whiskeredLoopClass_eq_one_iff
    (Dehn.squareRimLoop.map gamma.continuous)).mpr htrivial




theorem PLDomain.exists_new_frontier_spheres_or_marked_cut_fillings
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N F R C : Set X}
    (he : PLDomain e N) (hN : IsCompact N)
    (hF : IsCompact F) (hFne : F.Nonempty) (hFR : F ⊆ R)
    (hBF : Disjoint (frontier R) F) (hfront : frontier N = frontier R ∪ F)
    (hC : IsCompact C) (hBC : frontier R ⊆ C)
    (hprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' N))
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' N) =
      (Subtype.val : R → X) ⁻¹' F)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) :
    ∃ (n : ℕ) (S : Fin n → Set X), 0 < n ∧ (⋃ i, S i) = F ∧
      (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      (∀ i, IsCompact (S i) ∧ IsConnected (S i) ∧ S i ⊆ F ∧
        ∀ x ∈ S i, connectedComponentIn F x = S i) ∧
      ∀ i, Nonempty (ChartwisePLSphere e (S i)) ∨
        ∃ (d : ι × ↥(R \ C) → OpenPartialHomeomorph ↥(R \ C) V3) (P : Set ↥(R \ C)),
          PLDomain d P ∧
          (P = (Subtype.val : ↥(R \ C) → X) ⁻¹' N ∨
            P = (Subtype.val : ↥(R \ C) → X) ⁻¹' (interior N)ᶜ) ∧
          frontier P = (Subtype.val : ↥(R \ C) → X) ⁻¹' F ∧
          (∀ k, MapsTo (Subtype.val : ↥(R \ C) → X) (d k).source (e k.1).source) ∧
          (∀ k, (d k : ↥(R \ C) → V3) = (e k.1) ∘ Subtype.val) ∧
          ∃ (g : V2 → ↥(R \ C))
            (gamma : C(Q, ((Subtype.val : ↥(R \ C) → X) ⁻¹' F))),
            PolyhedralPLInCharts d g D ∧ MapsTo g D P ∧
            (∀ u : Q, g u = (gamma u : ↥(R \ C))) ∧
            FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 := by
  obtain ⟨hY, _, hcut⟩ :=
    Set.protected_open_cut_region hC.isClosed hBC hFR hprotect hrel hfront
  obtain ⟨n, S, hn, hcover, hdisj, hcomponents, halt⟩ :=
    he.exists_new_frontier_spheres_or_essential_proper_fillings hN hF hFne hFR
      hBF hfront hC hBC hprotect hrel hloops
  refine ⟨n, S, hn, hcover, hdisj, hcomponents, ?_⟩
  intro i
  rcases halt i with hsphere | ⟨f, rim, hrim, hproper, hessential⟩
  · exact Or.inl hsphere
  · exact Or.inr (he.exists_protected_marked_cut_filling hY hcut f rim hrim hproper hessential)

end PoincareConjecture.M76
