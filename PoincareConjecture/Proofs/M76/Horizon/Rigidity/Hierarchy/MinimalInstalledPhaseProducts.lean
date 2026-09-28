import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.MinimalPhaseSquareMaps
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.SquareMapRigidityAlternative
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedSubsetComponent

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

open Classical in
theorem exists_hamiltonZero_minimal_installed_phase_products {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hI : IsPLIrreducible e (latticeHandleDomain (Fin 0) (Fin 3) L0))
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    (∃ f : H0 ≃ₜ H0,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 0) (Fin 3) L0 f) ∧
      Nonempty (phi.HomotopyRel ⟨f, f.continuous⟩ B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel ⟨f, f.continuous⟩ B0)) ∨
    ∃ n, (∀ m, HamiltonZeroIncompressiblePhaseCount e d phi m → n ≤ m) ∧
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      ∃ psi : C(H0, H0),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
        let q := hamiltonZeroCircleMap psi
        let R := q ⁻¹' AddCircle.closedIntervalArc p a b
        PLDomain e R ∧ frontier R = q ⁻¹' {(a : C0), (b : C0)} ∧
        IsPLIrreducible e R ∧ IsPLIrreducible e (interior R)ᶜ ∧
        (∀ x : frontier R, Function.Injective
          (FundamentalGroup.map (VanKampen.inclusion (frontier R)) x)) ∧
        (∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X0)), ∀ x : T,
          Function.Injective (FundamentalGroup.map (VanKampen.inclusion T) x)) ∧
        (∀ theta ∈ ({(a : C0), (b : C0)} : Set C0),
          ∀ x : q ⁻¹' {theta}, Function.Injective (FundamentalGroup.map
            (VanKampen.inclusion (q ⁻¹' {theta})) x)) ∧
        (∃ (Nlower Nupper : Set X0)
          (lower : FrontierResidualModel e Nlower (q ⁻¹' {(a : C0)}))
          (upper : FrontierResidualModel e Nupper (q ⁻¹' {(b : C0)})),
          lower.count + upper.count = n ∧
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (lower.components i))) ∧
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (upper.components i))) ∧
          (∀ i (x : lower.components i), Nontrivial (FundamentalGroup (lower.components i) x)) ∧
          (∀ i (x : upper.components i), Nontrivial (FundamentalGroup (upper.components i) x))) ∧
        ∃ (s : Finset R) (r : ℝ), 0 < r ∧
          ∃ (J : Bool → SimplicialComplex ℝ (s → ℝ × V3))
            (c : Bool → (s → ℝ × V3) × ℝ → X0)
            (H : ∀ t : Bool, (J t).space ≃ₜ
              (q ⁻¹' {if t then (b : C0) else (a : C0)} : Set X0))
            (g : ∀ t, C((J t).space, C0 × C0)),
            (∀ t, (J t).faces.Finite) ∧
            (∀ t, PolyhedralPLInCharts e (c t) ((J t).space ×ˢ Icc (-r) r)) ∧
            (∀ t, IsEmbedding (fun z : (J t).space ×ˢ Icc (-r) r => c t z)) ∧
            (∀ t (x : (J t).space), c t (x, 0) = H t x) ∧
            (∀ t eps, 0 < eps → eps ≤ r →
              IsOpen (c t '' ((J t).space ×ˢ Ioo (-eps) eps))) ∧
            (∀ t, IsCoveringMap (g t)) ∧
            Disjoint (c false '' ((J false).space ×ˢ Icc (-r) r))
              (c true '' ((J true).space ×ˢ Icc (-r) r)) ∧
            (∀ t (x : (J t).space) u, u ∈ Icc (-r) r →
              Q0 (hamiltonZeroAmbientMap psi (c t (x, u))) =
                (g t x, (if t then (b : C0) else (a : C0)) +
                  (((if t then -1 else 1) * u : ℝ) : C0))) ∧
            (∀ t, IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
              (c t '' ((J t).space ×ˢ Ioo (-r) r))) ∧
            ∃ side : Bool, HamiltonZeroBoundaryFailureArc e
              (q ⁻¹' AddCircle.closedIntervalArc p
                (if side then b else a) (if side then a + p else b)) psi := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  obtain ⟨n, hmin, a, ha, b, hb, psi, hpsi, ⟨Hpsi⟩, ⟨Fpsi⟩,
    he, hfront, hIR, hIS, hfrontInj, hsides, hphases, residual,
    s, rho, hrho, hproducts⟩ :=
    exists_hamiltonZero_minimal_phase_square_maps e d hI hd phi hphi F
  have ha0 : 0 < a := by linarith [ha.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have hbp : b < p := by linarith [hb.2]
  have hcomp := circle_slab_closed_exterior_eq p (hamiltonZeroCircleMap psi)
    ha0 hab hbp hfront
  have hside (t : Bool) : hamiltonZeroCircleMap psi ⁻¹'
      AddCircle.closedIntervalArc p (if t then b else a) (if t then a + p else b) =
      (if t then (interior (hamiltonZeroCircleMap psi ⁻¹'
        AddCircle.closedIntervalArc p a b))ᶜ
      else hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) := by
    cases t
    · rfl
    · exact hcomp.symm
  have hsideI (t : Bool) : IsPLIrreducible e (hamiltonZeroCircleMap psi ⁻¹'
      AddCircle.closedIntervalArc p (if t then b else a) (if t then a + p else b)) := by
    rw [hside]
    cases t
    · exact hIR
    · exact hIS
  have hsideInj (t : Bool) : ∀ x : (hamiltonZeroCircleMap psi ⁻¹'
      AddCircle.closedIntervalArc p (if t then b else a) (if t then a + p else b)),
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(_, X0)) x) := by
    rw [hside]
    cases t <;> exact hsides _ (by simp)
  have hproducts' (t : Bool) := hproducts (if t then b else a) (by cases t <;> simp)
  choose J H c hJ hc hi hzero hopen hproduct u hu using hproducts'
  let η (t : Bool) := (J t).vertexAbstractComplex.edgeGraph.ConnectedComponent
  have hfinite (t : Bool) : Finite (η t) := by
    let : Finite (J t).vertices := ((J t).finite_vertices_of_finite_faces (hJ t)).to_subtype
    dsimp [η]
    infer_instance
  let : ∀ t, Finite (η t) := hfinite
  let K (t : Bool) (D : η t) := (J t).edgeComponentComplex D
  have hcover (t : Bool) : (⋃ D, (K t D).space) = (J t).space :=
    (J t).iUnion_edgeComponentComplex_space
  have hK (t : Bool) (D : η t) : (K t D).faces.Finite :=
    (hJ t).subset ((J t).edgeComponentComplex_le D)
  have hdis (t : Bool) : Pairwise fun D D' => Disjoint (K t D).space (K t D').space :=
    (J t).pairwise_disjoint_edgeComponentComplex_space
  let H' (t : Bool) : (J t).space ≃ₜ
      (hamiltonZeroCircleMap psi ⁻¹' {if t then (b : C0) else (a : C0)} : Set X0) :=
    (H t).trans (Homeomorph.setCongr (by cases t <;> rfl))
  have hzero' (t : Bool) (x : (J t).space) : c t (x, 0) = H' t x := by
    exact hzero t x
  have hphaseInj (t : Bool) :
      ∀ x : hamiltonZeroCircleMap psi ⁻¹' {if t then (b : C0) else (a : C0)},
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(_, X0)) x) :=
    hphases _ (by cases t <;> simp)
  have hproduct' (t : Bool) (x : (J t).space) (v : ℝ) (hv : v ∈ Icc (-rho) rho) :
      Q0 (hamiltonZeroAmbientMap psi (c t (x, v))) =
        ((Q0 (hamiltonZeroAmbientMap psi (c t (x, 0)))).1,
          (if t then (b : C0) else (a : C0)) +
            (((if t then -1 else 1) * v : ℝ) : C0)) := by
    rw [hzero]
    have hne : b ≠ a := hab.ne.symm
    cases t <;> simpa only [Bool.false_eq_true, if_false, if_true, ite_self, hne] using
      hproduct _ x v hv
  have alternative := exists_hamiltonZero_rigidity_or_boundary_failure_of_square_maps
    e d hd psi hpsi Fpsi ha0 hab hbp he hfront hsideI hsideInj J hJ hrho c hc hi
    hopen H' hzero' hphaseInj hproduct' K hcover hK hdis u
    (fun t D => by simpa only [show p = (64 : ℝ) by norm_num] using (hu t D).1)
    (fun t D => by simpa only [show p = (64 : ℝ) by norm_num] using (hu t D).2.1)
    (fun t D => by
      have hfib (q : ℝ) (hq : q = 64) : ∀ z w : PeriodicSquare.Square q,
          u t D (z.1, z.2) = u t D (w.1, w.2) ↔
            PeriodicSquare.projection q z = PeriodicSquare.projection q w := by
        subst q
        exact (hu t D).2.2
      exact hfib p (by norm_num))
  rcases alternative with ⟨f, hf, ⟨Hf⟩, Ff⟩ |
    ⟨r, hr, hrrho, g, psi', hpsi', ⟨Hpsi'⟩, Fpsi', hnormal,
      hg, hc', hi', hdis', hproduct'', hlocal, failure⟩
  · exact Or.inl ⟨f, hf, ⟨Hpsi.trans Hf⟩, Ff⟩
  · right
    refine ⟨n, hmin, a, ha, b, hb, psi', hpsi', ⟨Hpsi.trans Hpsi'⟩, Fpsi', ?_⟩
    dsimp only
    rw [hnormal]
    refine ⟨he, hfront, hIR, hIS, hfrontInj, hsides, hphases, residual,
      s, r, hr, J, c, H', g, hJ, hc', hi', hzero', ?_, hg, hdis', hproduct'',
      hlocal, ?_⟩
    · exact fun t eps heps hle => hopen t eps heps (hle.trans hrrho)
    · simpa only [hnormal] using failure

end PoincareConjecture.M76
