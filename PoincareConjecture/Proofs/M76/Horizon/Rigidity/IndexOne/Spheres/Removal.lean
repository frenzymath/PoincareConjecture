import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Geometry.BoundaryArcBall
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Maps.OriginalBallRemoval
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Maps.SlabExcision
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Topology.ExcisionInjection










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Q" => hamiltonOneHierarchyCoordinates
local notation "E" => latticeHandleDomainEquiv (Fin 1) (Fin 2) L

private instance : Fact (0 < p) := ⟨by norm_num⟩




theorem exists_closed_source_component_removal
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (hI : IsPLIrreducible e R)
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (he : PLDomain e (sourceSlab phi a b))
    (he' : PLDomain e (sourceSlab phi b (a + p)))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hfront' : frontier (sourceSlab phi b (a + p)) =
      (sourceSlab phi b (a + p) ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hinj : ∀ theta ∈ ({a, b} : Set ℝ), ∀ x : sourceSurface phi (theta : C),
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi (theta : C), X)) x))
    (hcorners : ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
      ∀ theta ∈ ({uv.1, uv.2} : Set ℝ),
        ∀ x ∈ sourceSurface phi (theta : C) ∩ frontier R,
          ∃ (ell lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
            ell.contLinear w = 1 ∧ ell.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
            x ∈ G.source ∧ ell (G x) = 0 ∧
            (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
            (∀ y ∈ G.source, y ∈ sourceSlab phi uv.1 uv.2 ↔ 0 ≤ ell (G y)) ∧
            (∀ y ∈ G.source, y ∈ sourceSlab phi uv.1 uv.2 ∩ frontier R ↔
              ell (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
            ∀ y ∈ G.source, y ∈ sourceSurface phi (theta : C) ↔
              ell (G y) = 0 ∧ lambda (G y) ≤ 0)
    {theta : ℝ} (htheta : theta ∈ ({a, b} : Set ℝ))
    {S : Set X} (hSne : S.Nonempty) (hS : S ⊆ sourceSurface phi (theta : C))
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi (theta : C)) x = S)
    (hrim : Disjoint S (frontier R)) :
    ∃ (psi : C(H, H)) (K : Set X) (T : phi.HomotopyRel psi B),
      IsCompact K ∧ K ⊆ interior R ∧ S ⊆ interior K ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∧
      Nonempty ((ContinuousMap.id H).HomotopyRel psi B) ∧
      (∀ (t : unitInterval) (x : H), ((E).symm x : X) ∉ interior K → T (t, x) = phi x) ∧
      (∀ (t : unitInterval) (x : H), (Q (T (t, x))).1 = (Q (phi x)).1) ∧
      psi ⁻¹' B = phi ⁻¹' B ∧ Disjoint S (sourceSurface psi (theta : C)) ∧
      (∀ s ∈ ({a, b} : Set ℝ),
        sourceSurface psi (s : C) = sourceSurface phi (s : C) \ K ∧
        ∀ x : sourceSurface psi (s : C), Function.Injective (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface psi (s : C), X)) x)) ∧
      PLDomain e (sourceSlab psi a b) ∧
      frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
        (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) ∧
      PLDomain e (sourceSlab psi b (a + p)) ∧
      frontier (sourceSlab psi b (a + p)) = (sourceSlab psi b (a + p) ∩ frontier R) ∪
        (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) ∧
      ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
        ∀ s ∈ ({uv.1, uv.2} : Set ℝ),
          ∀ x ∈ sourceSurface psi (s : C) ∩ frontier R,
            ∃ (ell lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
              ell.contLinear w = 1 ∧ ell.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
              x ∈ G.source ∧ ell (G x) = 0 ∧
              (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
              (∀ y ∈ G.source, y ∈ sourceSlab psi uv.1 uv.2 ↔ 0 ≤ ell (G y)) ∧
              (∀ y ∈ G.source, y ∈ sourceSlab psi uv.1 uv.2 ∩ frontier R ↔
                ell (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
              ∀ y ∈ G.source, y ∈ sourceSurface psi (s : C) ↔
                ell (G y) = 0 ∧ lambda (G y) ≤ 0 := by
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  have haI : a ∈ Ico (0 : ℝ) (0 + p) := ⟨ha.le, by linarith⟩
  have hbI : b ∈ Ico (0 : ℝ) (0 + p) := ⟨(ha.trans hab).le, by linarith⟩
  have hdis : Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C)) := by
    rw [sourceSurface_eq_inter_phase, sourceSurface_eq_inter_phase]
    apply disjoint_left.mpr
    intro x hx hy
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp (hx.2.symm.trans hy.2))
  obtain ⟨other, hpair, hfrontTheta, hdisTheta⟩ : ∃ other : C,
      (((theta : C) = (a : C) ∧ other = (b : C)) ∨
        ((theta : C) = (b : C) ∧ other = (a : C))) ∧
      frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (theta : C) ∪ sourceSurface phi other) ∧
      Disjoint (sourceSurface phi (theta : C)) (sourceSurface phi other) := by
    rcases htheta with rfl | rfl
    · exact ⟨(b : C), Or.inl ⟨rfl, rfl⟩, hfront, hdis⟩
    · exact ⟨(a : C), Or.inr ⟨rfl, rfl⟩, by simpa only [union_comm] using hfront,
        hdis.symm⟩
  obtain ⟨D, K, SK, _, ⟨ball⟩, _, hK, hKR, _, hSK, _, _, lower, upper,
      hlower, horder, hupper, hnota, hnotb, hboundary⟩ :=
    exists_closed_source_component_boundary_arc_ball e d phi hphi hI F0 ha hab hb hpair
      he hfrontTheta hdisTheta (hcorners (a, b) (Or.inl rfl) theta htheta)
      (hinj theta htheta) hSne hS hcomponent hrim isOpen_univ (subset_univ S)
  have hnotarc (s : ℝ) (hs : s ∈ ({a, b} : Set ℝ)) :
      (s : C) ∉ ((↑) : ℝ → C) '' Icc lower upper := by
    rintro ⟨z, hz, hzs⟩
    have hzI : z ∈ Ico (0 : ℝ) (0 + p) :=
      ⟨(hlower.trans_le hz.1).le, by linarith [hz.2]⟩
    rcases hs with rfl | rfl
    · exact hnota (((AddCircle.coe_eq_coe_iff_of_mem_Ico hzI haI).mp hzs) ▸ hz)
    · exact hnotb (((AddCircle.coe_eq_coe_iff_of_mem_Ico hzI hbI).mp hzs) ▸ hz)
  obtain ⟨psi, T, hpsi, hfixed, hcoord, hB, hrange, hphases⟩ :=
    exists_original_ball_phase_removal hd phi hphi ball hKR lower upper hlower horder hupper
      (by intro x hx; rw [← hboundary]; exact mem_image_of_mem _ hx)
  have hfixedK (x : H) (hx : ((E).symm x : X) ∉ K) : psi x = phi x :=
    (T.apply_one x).symm.trans (hfixed 1 x (fun hi => hx (interior_subset hi)))
  have havoid (x : R) (hx : (x : X) ∈ K) :
      sourcePhase psi (E x) ≠ (a : C) ∧ sourcePhase psi (E x) ≠ (b : C) := by
    have hr : sourcePhase psi (E x) ∈ ((↑) : ℝ → C) '' Icc lower upper :=
      hrange (E x) (by simpa only [Homeomorph.symm_apply_apply] using hx)
    exact ⟨fun h => hnotarc a (Or.inl rfl) (h ▸ hr),
      fun h => hnotarc b (Or.inr rfl) (h ▸ hr)⟩
  have hretained (s : ℝ) (hs : s ∈ ({a, b} : Set ℝ)) :
      sourceSurface psi (s : C) = sourceSurface phi (s : C) \ K :=
    hphases (s : C) (hnotarc s hs)
  have hfrontK (s : ℝ) (hs : s ∈ ({a, b} : Set ℝ)) :
      Disjoint (sourceSurface phi (s : C)) (frontier K) := by
    apply disjoint_left.mpr
    intro x hx hxK
    rw [ball.frontier_eq] at hxK
    have hxarc : ambientSourcePhase phi x ∈ ((↑) : ℝ → C) '' Icc lower upper := by
      rw [← hboundary]
      exact mem_image_of_mem _ hxK
    rw [sourceSurface_eq_inter_phase] at hx
    exact hnotarc s hs (hx.2 ▸ hxarc)
  have hinjNew (s : ℝ) (hs : s ∈ ({a, b} : Set ℝ)) :
      ∀ x : sourceSurface psi (s : C), Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface psi (s : C), X)) x) := by
    rw [hretained s hs]
    exact FundamentalGroup.ambient_injective_sdiff_of_disjoint_frontier
      hK.isClosed (hfrontK s hs) (hinj s hs)
  obtain ⟨heNew, hfNew, heNew', hfNew'⟩ :=
    plDomains_complementary_sourceSlabs_of_supported_phase_avoidance phi psi
      (c := 0) ha hab (by simpa only [zero_add] using hb) he he' hfront hfront'
      hK.isClosed hKR hfixedK havoid
  refine ⟨psi, K, T, hK, hKR, hSK, hpsi, ⟨F0.trans T⟩, hfixed, hcoord, hB, ?_,
    (fun s hs => ⟨hretained s hs, hinjNew s hs⟩), heNew, hfNew, heNew', hfNew', ?_⟩
  · rw [hretained theta htheta]
    exact disjoint_left.mpr fun x hx hy => hy.2 (interior_subset (hSK hx))
  · intro uv huv s hs x hx
    have hxK : x ∉ K := fun h => hx.2.2 (hKR h)
    have hxold : x ∈ sourceSurface phi (s : C) :=
      (sourceSurface_agrees_off_support phi psi hfixedK (s : C) x hxK).mp hx.1
    exact exists_transverse_marked_corner_of_supported_map e phi psi hK.isClosed hKR hfixedK
      uv.1 uv.2 (s : C) hx.2 (hcorners uv huv s hs x ⟨hxold, hx.2⟩)

end PoincareConjecture.M76.HamiltonIntervalTorus
