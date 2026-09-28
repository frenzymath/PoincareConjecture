import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.Compression.OriginalSphericalSlabReduction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Compression.OriginalWideSlabResidualDecrease
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.OriginalSlabProperDisks
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.ComplementarySlabDomains

set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

private instance period_positive : Fact (0 < p) := ⟨by norm_num⟩

private def castPhaseModel {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {N A B : Set X0} (h : A = B) (M : FrontierResidualModel e N A) :
    FrontierResidualModel e N B := h ▸ M

private theorem castPhaseModel_complexity {ι : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3} {N A B : Set X0}
    (h : A = B) (M : FrontierResidualModel e N A) :
    (castPhaseModel h M).complexity = M.complexity := by
  cases h
  rfl

private structure SourceNonsphericalStage {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3) (phi : C(H0, H0)) (a b : ℝ) where
  map : C(H0, H0)
  pl : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 map)
  fromOriginal : phi.HomotopyRel map B0
  fromIdentity : (ContinuousMap.id H0).HomotopyRel map B0
  domain : PLDomain e (hamiltonZeroCircleMap map ⁻¹' AddCircle.closedIntervalArc p a b)
  frontier_eq : frontier (hamiltonZeroCircleMap map ⁻¹' AddCircle.closedIntervalArc p a b) =
    hamiltonZeroCircleMap map ⁻¹' {(a : C0), (b : C0)}
  lowerDomain : Set X0
  upperDomain : Set X0
  lowerModel : FrontierResidualModel e lowerDomain (hamiltonZeroCircleMap map ⁻¹' {(a : C0)})
  upperModel : FrontierResidualModel e upperDomain (hamiltonZeroCircleMap map ⁻¹' {(b : C0)})

private def SourceNonsphericalStage.complexity {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    {phi : C(H0, H0)} {a b : ℝ} (s : SourceNonsphericalStage e d phi a b) : ℕ :=
  s.lowerModel.complexity + s.upperModel.complexity

theorem exists_hamiltonZero_nonspherical_incompressible_slab {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hI : IsPLIrreducible e (latticeHandleDomain (Fin 0) (Fin 3) L0))
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      ∃ psi : C(H0, H0),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
        let R := hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b
        PLDomain e R ∧ frontier R = hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)} ∧
        ∃ (Nlower Nupper : Set X0)
          (lower : FrontierResidualModel e Nlower (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}))
          (upper : FrontierResidualModel e Nupper (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)})),
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (lower.components i))) ∧
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (upper.components i))) ∧
        ∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X0)),
          ∀ theta ∈ ({(a : C0), (b : C0)} : Set C0),
            ∃ hMT : hamiltonZeroCircleMap psi ⁻¹' {theta} ⊆ T,
              ∀ x : hamiltonZeroCircleMap psi ⁻¹' {theta},
                Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hMT) x) := by
  classical
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  obtain ⟨a, haI, b, hbI, ha, hab, hb, hR, he, hfront, _, _, _, _⟩ :=
    exists_hamiltonZero_slab_proper_disk_alternative e d hd phi hphi F
  have habq : (a : C0) ≠ (b : C0) := by
    intro h
    have haP : a ∈ Ico (0 : ℝ) (0 + p) := ⟨ha.le, by linarith⟩
    have hbP : b ∈ Ico (0 : ℝ) (0 + p) := ⟨by linarith, by linarith⟩
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haP hbP).mp h)
  have hmodels (theta other : C0) (hne : other ≠ theta)
      (hfrontier : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) =
        (hamiltonZeroCircleMap phi ⁻¹' {other}) ∪ (hamiltonZeroCircleMap phi ⁻¹' {theta})) :
      Nonempty (FrontierResidualModel e
        (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
        (hamiltonZeroCircleMap phi ⁻¹' {theta})) := by
    have hphase : (hamiltonZeroCircleMap phi ⁻¹' {theta}).Nonempty := by
      obtain ⟨x, hx⟩ := surjective_hamiltonZeroCircleMap phi F theta
      exact ⟨x, hx⟩
    have hsub : hamiltonZeroCircleMap phi ⁻¹' {theta} ⊆
        hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b := by
      intro x hx
      exact he.closed.frontier_subset (hfrontier.symm ▸ Or.inr hx)
    exact he.nonempty_frontier_residual_model hR (hphase.mono hsub)
      (isClosed_singleton.preimage (hamiltonZeroCircleMap phi).continuous)
      (isClosed_singleton.preimage (hamiltonZeroCircleMap phi).continuous)
      (Set.disjoint_left.mpr (fun x hxo hxt => hne (hxo.symm.trans hxt))) hfrontier hphase
  obtain ⟨lowerModel⟩ := hmodels (a : C0) (b : C0) habq.symm (by rw [hfront]; ext x; simp [or_comm])
  obtain ⟨upperModel⟩ := hmodels (b : C0) (a : C0) habq (by rw [hfront]; ext x; simp)
  let initial : SourceNonsphericalStage e d phi a b :=
    ⟨phi, hphi, ContinuousMap.HomotopyRel.refl phi B0, F, he, hfront,
      _, _, lowerModel, upperModel⟩
  have hex : ∃ n : ℕ, ∃ s : SourceNonsphericalStage e d phi a b, s.complexity = n :=
    ⟨initial.complexity, initial, rfl⟩
  obtain ⟨s0, hs0⟩ := Nat.find_spec hex
  have hexCount : ∃ n : ℕ, ∃ s : SourceNonsphericalStage e d phi a b,
      s.complexity = Nat.find hex ∧ s.lowerModel.count + s.upperModel.count = n :=
    ⟨s0.lowerModel.count + s0.upperModel.count, s0, hs0, rfl⟩
  obtain ⟨s, hs, hsCount⟩ := Nat.find_spec hexCount
  have hminimal (t : SourceNonsphericalStage e d phi a b) : s.complexity ≤ t.complexity := by
    rw [hs]
    exact Nat.find_min' hex ⟨t, rfl⟩
  have hcountminimal (t : SourceNonsphericalStage e d phi a b)
      (ht : t.complexity = s.complexity) :
      s.lowerModel.count + s.upperModel.count ≤ t.lowerModel.count + t.upperModel.count := by
    rw [hsCount]
    exact Nat.find_min' hexCount ⟨t, ht.trans hs, rfl⟩
  have lower_impossible (psi : C(H0, H0))
      (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
      (H : s.map.HomotopyRel psi B0) (Fpsi : (ContinuousMap.id H0).HomotopyRel psi B0)
      (hdomain : PLDomain e (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
      (hfrontier : frontier (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
        hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)})
      (hupper : hamiltonZeroCircleMap psi ⁻¹' {(b : C0)} = hamiltonZeroCircleMap s.map ⁻¹' {(b : C0)})
      {Nnew : Set X0} (newModel : FrontierResidualModel e Nnew (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}))
      (hdecrease : newModel.complexity < s.lowerModel.complexity) : False := by
    let t : SourceNonsphericalStage e d phi a b :=
      ⟨psi, hpsi, s.fromOriginal.trans H, Fpsi, hdomain, hfrontier,
        Nnew, s.upperDomain, newModel, castPhaseModel hupper.symm s.upperModel⟩
    have hmin := hminimal t
    change s.lowerModel.complexity + s.upperModel.complexity ≤
      newModel.complexity + (castPhaseModel hupper.symm s.upperModel).complexity at hmin
    rw [castPhaseModel_complexity] at hmin
    omega
  have upper_impossible (psi : C(H0, H0))
      (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
      (H : s.map.HomotopyRel psi B0) (Fpsi : (ContinuousMap.id H0).HomotopyRel psi B0)
      (hdomain : PLDomain e (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
      (hfrontier : frontier (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
        hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)})
      (hlower : hamiltonZeroCircleMap psi ⁻¹' {(a : C0)} = hamiltonZeroCircleMap s.map ⁻¹' {(a : C0)})
      {Nnew : Set X0} (newModel : FrontierResidualModel e Nnew (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)}))
      (hdecrease : newModel.complexity < s.upperModel.complexity) : False := by
    let t : SourceNonsphericalStage e d phi a b :=
      ⟨psi, hpsi, s.fromOriginal.trans H, Fpsi, hdomain, hfrontier,
        s.lowerDomain, Nnew, castPhaseModel hlower.symm s.lowerModel, newModel⟩
    have hmin := hminimal t
    change s.lowerModel.complexity + s.upperModel.complexity ≤
      (castPhaseModel hlower.symm s.lowerModel).complexity + newModel.complexity at hmin
    rw [castPhaseModel_complexity] at hmin
    omega
  have hlower_nonspherical (i : Fin s.lowerModel.count) :
      ¬ Nonempty (ChartwisePLSphere e (s.lowerModel.components i)) := by
    rintro ⟨sph⟩
    obtain ⟨psi, hpsi, ⟨H⟩, ⟨Fpsi⟩, hdomain, hfrontier, lowerNew, upperNew, hc, hn⟩ :=
      s.pl.exists_hamiltonZero_original_spherical_slab_reduction hI hd s.fromIdentity
        ha hab hb s.domain s.frontier_eq s.lowerModel s.upperModel a (Or.inl rfl)
        s.lowerModel i sph
    let t : SourceNonsphericalStage e d phi a b :=
      ⟨psi, hpsi, s.fromOriginal.trans H, Fpsi, hdomain, hfrontier,
        s.lowerDomain, s.upperDomain, lowerNew, upperNew⟩
    have ht : t.complexity = s.complexity := le_antisymm hc (hminimal t)
    exact Nat.not_lt_of_ge (hcountminimal t ht) hn
  have hupper_nonspherical (i : Fin s.upperModel.count) :
      ¬ Nonempty (ChartwisePLSphere e (s.upperModel.components i)) := by
    rintro ⟨sph⟩
    obtain ⟨psi, hpsi, ⟨H⟩, ⟨Fpsi⟩, hdomain, hfrontier, lowerNew, upperNew, hc, hn⟩ :=
      s.pl.exists_hamiltonZero_original_spherical_slab_reduction hI hd s.fromIdentity
        ha hab hb s.domain s.frontier_eq s.lowerModel s.upperModel b (Or.inr rfl)
        s.upperModel i sph
    let t : SourceNonsphericalStage e d phi a b :=
      ⟨psi, hpsi, s.fromOriginal.trans H, Fpsi, hdomain, hfrontier,
        s.lowerDomain, s.upperDomain, lowerNew, upperNew⟩
    have ht : t.complexity = s.complexity := le_antisymm hc (hminimal t)
    exact Nat.not_lt_of_ge (hcountminimal t ht) hn
  have hcomplement := circle_slab_closed_exterior_eq p (hamiltonZeroCircleMap s.map)
    ha hab hb s.frontier_eq
  have hcompdomain : PLDomain e
      (hamiltonZeroCircleMap s.map ⁻¹' AddCircle.closedIntervalArc p b (a + p)) :=
    hcomplement ▸ s.domain.closed_exterior
  have hcompfront : frontier
      (hamiltonZeroCircleMap s.map ⁻¹' AddCircle.closedIntervalArc p b (a + p)) =
      hamiltonZeroCircleMap s.map ⁻¹' {(a : C0), (b : C0)} := by
    rw [← hcomplement, s.domain.frontier_closed_exterior, s.frontier_eq]
  have hcompfront' : frontier
      (hamiltonZeroCircleMap s.map ⁻¹' AddCircle.closedIntervalArc p b (a + p)) =
      hamiltonZeroCircleMap s.map ⁻¹' {(b : C0), ((a + p : ℝ) : C0)} := by
    simpa only [AddCircle.coe_add_period, Set.pair_comm] using hcompfront
  have hca : (a + b) / 2 < b := by linarith
  have hcb : b < a + p := by linarith
  have hcc : a + p < (a + b) / 2 + 64 := by linarith
  refine ⟨a, haI, b, hbI, s.map, s.pl, ⟨s.fromOriginal⟩, ⟨s.fromIdentity⟩,
    s.domain, s.frontier_eq, s.lowerDomain, s.upperDomain, s.lowerModel, s.upperModel,
    hlower_nonspherical, hupper_nonspherical, ?_⟩
  intro T hT theta htheta
  rcases hT with rfl | hT
  · have hMfront : hamiltonZeroCircleMap s.map ⁻¹' {theta} ⊆
        frontier (hamiltonZeroCircleMap s.map ⁻¹' AddCircle.closedIntervalArc p a b) := by
      intro x hx
      rw [s.frontier_eq]
      change hamiltonZeroCircleMap s.map x ∈ ({(a : C0), (b : C0)} : Set C0)
      change hamiltonZeroCircleMap s.map x = theta at hx
      rw [hx]
      exact htheta
    have hMR := hMfront.trans s.domain.closed.frontier_subset
    refine ⟨hMR, ?_⟩
    intro x
    obtain hinj | ⟨j, rim, hj, hemb, hDR, hrim, hproper, hessential⟩ :=
      injective_or_exists_marked_proper_disk e s.domain hMR hMfront
        (isOpen_boundary_phase_of_frontier_eq (hamiltonZeroCircleMap s.map)
          habq s.frontier_eq htheta) x
    · exact hinj
    · rcases htheta with rfl | htheta
      · obtain ⟨psi, hpsi, ⟨H⟩, ⟨Fpsi⟩, hdomain, hfrontier, hother, _, newModel, hdecrease⟩ :=
          s.pl.exists_hamiltonZero_wide_lower_residual_decrease hd s.fromIdentity
            (c := 0) ha hab (by linarith) s.domain s.frontier_eq s.lowerModel
            hj hemb hDR hproper rim hrim hessential
        exact (lower_impossible psi hpsi H Fpsi hdomain hfrontier hother newModel hdecrease).elim
      · have ht : theta = (b : C0) := htheta
        subst theta
        obtain ⟨psi, hpsi, ⟨H⟩, ⟨Fpsi⟩, hdomain, hfrontier, hother, _, newModel, hdecrease⟩ :=
          s.pl.exists_hamiltonZero_wide_upper_residual_decrease hd s.fromIdentity
            (c := 0) ha hab (by linarith) s.domain s.frontier_eq s.upperModel
            hj hemb hDR hproper rim hrim hessential
        exact (upper_impossible psi hpsi H Fpsi hdomain hfrontier hother newModel hdecrease).elim
  · have hTeq : T = (interior (hamiltonZeroCircleMap s.map ⁻¹' AddCircle.closedIntervalArc p a b))ᶜ := hT
    rw [hTeq, hcomplement]
    have hMfront : hamiltonZeroCircleMap s.map ⁻¹' {theta} ⊆
        frontier (hamiltonZeroCircleMap s.map ⁻¹' AddCircle.closedIntervalArc p b (a + p)) := by
      intro x hx
      rw [hcompfront]
      change hamiltonZeroCircleMap s.map x ∈ ({(a : C0), (b : C0)} : Set C0)
      change hamiltonZeroCircleMap s.map x = theta at hx
      rw [hx]
      exact htheta
    have hMR := hMfront.trans hcompdomain.closed.frontier_subset
    refine ⟨hMR, ?_⟩
    intro x
    obtain hinj | ⟨j, rim, hj, hemb, hDR, hrim, hproper, hessential⟩ :=
      injective_or_exists_marked_proper_disk e hcompdomain hMR hMfront
        (isOpen_boundary_phase_of_frontier_eq (hamiltonZeroCircleMap s.map)
          habq hcompfront htheta) x
    · exact hinj
    · rcases htheta with rfl | htheta
      · have step := s.pl.exists_hamiltonZero_wide_upper_residual_decrease hd s.fromIdentity
          hca hcb hcc hcompdomain hcompfront' (Nold := s.lowerDomain) (j := j)
        rw [AddCircle.coe_add_period p a] at step
        obtain ⟨psi, hpsi, ⟨H⟩, ⟨Fpsi⟩, heComp, hfComp, hother, _, newModel, hdecrease⟩ :=
          step s.lowerModel hj hemb hDR hproper rim hrim hessential
        have hfComp' : frontier
            (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p b (a + p)) =
            hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)} := by
          simpa only [Set.pair_comm] using hfComp
        obtain ⟨hdomain, hfrontier, _⟩ := PLDomain.circle_slab_of_complementary p
          (hamiltonZeroCircleMap psi) ha hab hb heComp hfComp'
        exact (lower_impossible psi hpsi H Fpsi hdomain hfrontier hother newModel hdecrease).elim
      · have ht : theta = (b : C0) := htheta
        subst theta
        have hout := s.pl.exists_hamiltonZero_wide_lower_residual_decrease hd s.fromIdentity
          hca hcb hcc hcompdomain hcompfront' s.upperModel hj hemb hDR hproper rim hrim hessential
        simp only [AddCircle.coe_add_period] at hout
        obtain ⟨psi, hpsi, ⟨H⟩, ⟨Fpsi⟩, heComp, hfComp, hother, _, newModel, hdecrease⟩ := hout
        have hfComp' : frontier
            (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p b (a + p)) =
            hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)} := by
          simpa only [Set.pair_comm] using hfComp
        obtain ⟨hdomain, hfrontier, _⟩ := PLDomain.circle_slab_of_complementary p
          (hamiltonZeroCircleMap psi) ha hab hb heComp hfComp'
        exact (upper_impossible psi hpsi H Fpsi hdomain hfrontier hother newModel hdecrease).elim

end PoincareConjecture.M76
