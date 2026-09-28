import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.TwoPhaseCoveringInstallation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.FirstSlabAlternativeRigidity










set_option autoImplicit false
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

theorem exists_hamiltonZero_rigidity_or_boundary_failure_of_square_maps
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {η : Bool → Type*} [∀ s, Finite (η s)]
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {alpha beta : ℝ} (ha : 0 < alpha) (hab : alpha < beta) (hb : beta < p)
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta) =
      hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
    (hI : ∀ side : Bool, IsPLIrreducible e (hamiltonZeroCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then beta else alpha) (if side then alpha + p else beta)))
    (hinj : ∀ side : Bool, ∀ x : (hamiltonZeroCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then beta else alpha) (if side then alpha + p else beta)),
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(_, X0)) x))
    (J : Bool → SimplicialComplex ℝ E) (hJ : ∀ s, (J s).faces.Finite)
    {rho : ℝ} (hrho : 0 < rho) (c : Bool → E × ℝ → X0)
    (hc : ∀ s, PolyhedralPLInCharts e (c s) ((J s).space ×ˢ Icc (-rho) rho))
    (hi : ∀ s, IsEmbedding (fun z : (J s).space ×ˢ Icc (-rho) rho => c s z))
    (hopen : ∀ s eps, 0 < eps → eps ≤ rho →
      IsOpen (c s '' ((J s).space ×ˢ Ioo (-eps) eps)))
    (H : ∀ s, (J s).space ≃ₜ
      (hamiltonZeroCircleMap phi ⁻¹' {if s then (beta : C0) else (alpha : C0)} : Set X0))
    (hzero : ∀ s (x : (J s).space), c s (x, 0) = H s x)
    (hphaseInj : ∀ s : Bool,
      ∀ x : hamiltonZeroCircleMap phi ⁻¹' {if s then (beta : C0) else (alpha : C0)},
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(_, X0)) x))
    (hproduct : ∀ s (x : (J s).space) t, t ∈ Icc (-rho) rho →
      Q0 (hamiltonZeroAmbientMap phi (c s (x, t))) =
        ((Q0 (hamiltonZeroAmbientMap phi (c s (x, 0)))).1,
          (if s then (beta : C0) else (alpha : C0)) +
            (((if s then -1 else 1) * t : ℝ) : C0)))
    (K : ∀ s, η s → SimplicialComplex ℝ E)
    (hcover : ∀ s, (⋃ i, (K s i).space) = (J s).space)
    (hK : ∀ s i, (K s i).faces.Finite)
    (hdisjoint : ∀ s, Pairwise fun i j => Disjoint (K s i).space (K s j).space)
    (u : ∀ s, η s → ℝ × ℝ → E)
    (hu : ∀ s i, FinitePiecewiseAffineOn (u s i) (Icc 0 p ×ˢ Icc 0 p))
    (himage : ∀ s i, u s i '' (Icc 0 p ×ˢ Icc 0 p) = (K s i).space)
    (hfib : ∀ s i (z w : PeriodicSquare.Square p),
      u s i (z.1, z.2) = u s i (w.1, w.2) ↔
        PeriodicSquare.projection p z = PeriodicSquare.projection p w) :
    (∃ f : H0 ≃ₜ H0,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 0) (Fin 3) L0 f) ∧
      Nonempty (phi.HomotopyRel ⟨f, f.continuous⟩ B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel ⟨f, f.continuous⟩ B0)) ∨
    ∃ r : ℝ, 0 < r ∧ r ≤ rho ∧
      ∃ (g : ∀ s, C((J s).space, C0 × C0)) (psi : C(H0, H0)),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
        hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
        (∀ s, IsCoveringMap (g s)) ∧
        (∀ s, PolyhedralPLInCharts e (c s) ((J s).space ×ˢ Icc (-r) r)) ∧
        (∀ s, IsEmbedding (fun z : (J s).space ×ˢ Icc (-r) r => c s z)) ∧
        Disjoint (c false '' ((J false).space ×ˢ Icc (-r) r))
          (c true '' ((J true).space ×ˢ Icc (-r) r)) ∧
        (∀ s (x : (J s).space) t, t ∈ Icc (-r) r →
          Q0 (hamiltonZeroAmbientMap psi (c s (x, t))) =
            (g s x, (if s then (beta : C0) else (alpha : C0)) +
              (((if s then -1 else 1) * t : ℝ) : C0))) ∧
        (∀ s, IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
          (c s '' ((J s).space ×ˢ Ioo (-r) r))) ∧
        ∃ side : Bool, HamiltonZeroBoundaryFailureArc e
          (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p
            (if side then beta else alpha) (if side then alpha + p else beta)) psi := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hleft (z : E × ℝ) (hz : z ∈ (J false).space ×ˢ Icc (-rho) rho) :
      hamiltonZeroCircleMap phi (c false z) = ((alpha + z.2 : ℝ) : C0) := by
    have h := congrArg Prod.snd (hproduct false ⟨z.1, hz.1⟩ z.2 hz.2)
    simpa only [hamiltonZeroAmbientMap_circle, Bool.false_eq_true, if_false, one_mul,
      Prod.snd, AddCircle.coe_add] using h
  have hright (z : E × ℝ) (hz : z ∈ (J true).space ×ˢ Icc (-rho) rho) :
      hamiltonZeroCircleMap phi (c true z) = ((beta - z.2 : ℝ) : C0) := by
    have h := congrArg Prod.snd (hproduct true ⟨z.1, hz.1⟩ z.2 hz.2)
    simpa only [hamiltonZeroAmbientMap_circle, if_true, neg_one_mul, Prod.snd,
      sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg] using h
  obtain ⟨r, hr, hrrho, _, _, _, hsub, hdis, _⟩ :=
    exists_disjoint_inward_phase_collar_radius p (hamiltonZeroCircleMap phi)
      (fun s => (J s).space) c hrho ha hab hb hleft hright
  have hcr (s : Bool) : PolyhedralPLInCharts e (c s) ((J s).space ×ˢ Icc (-r) r) := by
    obtain ⟨L, hL, hLs⟩ := (J s).exists_finite_interval_product (hJ s) (by linarith : -r < r)
    rw [← hLs]
    exact (hc s).restrict_finite L hL (hLs.subset.trans (hsub s))
  have hir (s : Bool) : IsEmbedding (fun z : (J s).space ×ˢ Icc (-r) r => c s z) :=
    (hi s).comp (IsEmbedding.inclusion (hsub s))
  obtain ⟨g, psi, A, hg, _, _, hpsi, ⟨Hpsi⟩, ⟨Fpsi⟩, hnormal, _, hfull, hlocal⟩ :=
    exists_hamiltonZero_two_phase_coverings_of_square_maps hd phi hphi F J hJ hr c hcr hir
      (fun s eps heps hle => hopen s eps heps (hle.trans hrrho)) hdis
      (fun s => if s then (beta : C0) else (alpha : C0)) (fun s => if s then -1 else 1)
      (by intro s; cases s <;> norm_num) H hzero hphaseInj
      (fun s x t ht => hproduct s x t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      K hcover hK hdisjoint u hu himage hfib
  have hquarter (s : Bool) : (J s).space ×ˢ Icc (-(r / 4)) (r / 4) ⊆
      (J s).space ×ˢ Icc (-r) r := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hiq (s : Bool) : IsEmbedding
      (fun z : (J s).space ×ˢ Icc (-(r / 4)) (r / 4) => c s z) :=
    (hir s).comp (IsEmbedding.inclusion (hquarter s))
  have hcq (s : Bool) : PolyhedralPLInCharts e (c s) ((J s).space ×ˢ Icc (-(r / 4)) (r / 4)) := by
    obtain ⟨L, hL, hLs⟩ := (J s).exists_finite_interval_product (hJ s)
      (by linarith : -(r / 4) < r / 4)
    rw [← hLs]
    exact (hcr s).restrict_finite L hL (hLs.subset.trans (hquarter s))
  have hphase (s : Bool) :
      (hamiltonZeroCircleMap phi ⁻¹' {if s then (beta : C0) else (alpha : C0)} : Set X0) =
        hamiltonZeroCircleMap psi ⁻¹' {if s then (beta : C0) else (alpha : C0)} := by
    rw [hnormal]
  let H' (s : Bool) := (H s).trans (Homeomorph.setCongr (hphase s))
  have he' : PLDomain e (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta) := by
    rw [hnormal]; exact he
  have hfront' : frontier (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta) =
      hamiltonZeroCircleMap psi ⁻¹' {(alpha : C0), (beta : C0)} := by
    rw [hnormal]; exact hfront
  have hI' (side : Bool) : IsPLIrreducible e (hamiltonZeroCircleMap psi ⁻¹'
      AddCircle.closedIntervalArc p (if side then beta else alpha) (if side then alpha + p else beta)) := by
    rw [hnormal]; exact hI side
  have hinj' (side : Bool) : ∀ x : (hamiltonZeroCircleMap psi ⁻¹'
      AddCircle.closedIntervalArc p (if side then beta else alpha) (if side then alpha + p else beta)),
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(_, X0)) x) := by
    rw [hnormal]; exact hinj side
  have alternative := exists_hamiltonZero_rigidity_or_first_boundary_failure e d hd psi hpsi Fpsi
    ha hab hb he' hfront' hI' hinj' (fun s => (J s).space)
    (fun s => (J s).isCompact_space_of_finite (hJ s)) (by linarith : 0 < r / 4) c hiq
    (fun s eps heps hle => hopen s eps heps (by linarith)) H'
    (fun s x => hzero s x) g hg hfull
  rcases alternative with ⟨f, hf, ⟨Hf⟩, Ff⟩ | failure
  · exact Or.inl ⟨f, hf, ⟨Hpsi.trans Hf⟩, Ff⟩
  · exact Or.inr ⟨r / 4, by linarith, by linarith, g, psi, hpsi, ⟨Hpsi⟩, ⟨Fpsi⟩,
      hnormal, hg, hcq, hiq,
      hdis.mono (image_mono (hquarter false)) (image_mono (hquarter true)),
      hfull, hlocal, failure⟩

end PoincareConjecture.M76
