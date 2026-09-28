import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.SourceRimExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.MarkedStraightening
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.MarkedCoveringPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.FoldedContraction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.CoordinateHomotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.SourceRimLift
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInterior
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SquareAnnulusBoundary

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "C" => annulusCylinderHomeomorph

theorem finitePiecewiseAffineOn_annulus_radial_interval (z : Circle) :
    FinitePiecewiseAffineOn (fun t : ℝ => annulusMap 8 (by norm_num) (z, 2 * t - 1))
      (Icc (0 : ℝ) 1) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let s : ℝ := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
  have hs : s ∈ Icc (0 : ℝ) (4 * 8) := by
    have h := (AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property
    exact ⟨h.1, by dsimp [s]; linarith [h.2]⟩
  have hsz : (s : Circle) = z := AddCircle.coe_equivIco
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  let A : ℝ →ᴬ[ℝ] (ℝ × ℝ) := (ContinuousAffineMap.const ℝ ℝ s).prod
    ((2 : ℝ) • ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ 1)
  have hA : FinitePiecewiseAffineOn A (Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKI, K.affineOnFaces_affine A⟩
  have h := (finitePiecewiseAffineOn_wrappedStripMap
    (L := 8) (d := 1) (by norm_num) (by norm_num)).comp hA (by
      intro t ht
      change (s, 2 * t - 1) ∈ rectangle (4 * 8) 1
      exact ⟨hs, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩)
  apply h.congr
  intro t ht
  change wrappedStripMap 8 (s, 2 * t - 1) = _
  rw [← hsz]
  exact (annulusMap_coe (L := 8) (t := 2 * t - 1) (s := s)
    (by norm_num) (by
      have hh : |2 * t - 1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      linarith) hs).symm

theorem finitePL_annulus_mem_rims_iff (D : Ann ≃ₜ Ann) (hD : D.IsFinitePL) (z : Ann) :
    D z ∈ annulusRims ↔ z ∈ annulusRims := by
  have hrim (x : Ann) : x ∈ annulusRims ↔ (x : ℝ × ℝ) ∈ frontier Ann := by
    rw [annulusRims, mem_union, range_annulusRimPoint, range_annulusRimPoint]
    rw [mem_frontier_squareAnnulus_iff (by norm_num) (by norm_num) x.property]
    change depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1 ↔
      |depth 8 (x : ℝ × ℝ)| = 1
    exact or_comm.trans (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).symm
  rw [hrim, hrim, mem_frontier_iff_notMem_interior (D z).property,
    mem_frontier_iff_notMem_interior z.property, hD.mem_interior_iff rfl]

theorem exists_marked_finitePL_vertical_arc_family
    (D : Ann ≃ₜ Ann) (hD : D.IsFinitePL) (g : C(Circle, C0)) (hg : IsCoveringMap g)
    (c : C(Ann, unitInterval × C0))
    (hformula : ∀ x : Ann, (c x).2 = g ((C).symm (D x)).2) (xi : C0) :
    ∃ (n : ℕ) (arc : Fin n → C(unitInterval, Ann)) (a : Fin n → ℝ → ℝ × ℝ),
      (∀ i, Topology.IsEmbedding (arc i)) ∧
      (∀ i, FinitePiecewiseAffineOn (a i) (Icc (0 : ℝ) 1)) ∧
      (∀ i (t : unitInterval), a i t = (arc i t : ℝ × ℝ)) ∧
      Pairwise (fun i k => Disjoint (range (arc i)) (range (arc k))) ∧
      (⋃ i, range (arc i)) = {x | (c x).2 = xi} ∧
      ∀ i t, arc i t ∈ annulusRims ↔ t = 0 ∨ t = 1 := by
  classical
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let B : Set Circle := g ⁻¹' {xi}
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    ((isClosed_singleton.preimage g.continuous).isCompact)
  let : DiscreteTopology B := (hg xi).discreteTopology_fiber
  let : Finite B := finite_of_compact_of_discrete
  let : Fintype B := Fintype.ofFinite B
  let arc (z : B) : C(unitInterval, Ann) :=
    ⟨fun t => D.symm ((C) (t, z)), by fun_prop⟩
  obtain ⟨fD, hfD, hfDv⟩ := hD.symm
  let a (z : B) : ℝ → ℝ × ℝ :=
    fun t => fD (annulusMap 8 (by norm_num) ((z : Circle), 2 * t - 1))
  have hav (z : B) (t : unitInterval) : a z t = (arc z t : ℝ × ℝ) := by
    change fD (annulusMap 8 (by norm_num) ((z : Circle), 2 * (t : ℝ) - 1)) = _
    have h := (hfDv ((C) (t, z))).symm
    rw [annulusCylinderHomeomorph_apply] at h
    change fD _ = (D.symm ((C) (t, z)) : ℝ × ℝ)
    rw [annulusCylinderHomeomorph_apply]
    exact h
  have ha (z : B) : FinitePiecewiseAffineOn (a z) (Icc (0 : ℝ) 1) := by
    apply hfD.comp (finitePiecewiseAffineOn_annulus_radial_interval z)
    intro t ht
    exact (annulusRimCylinder (⟨t, ht⟩, z)).property
  have hi (z : B) : Topology.IsEmbedding (arc z) := by
    apply (arc z).continuous.isClosedEmbedding ?_ |>.isEmbedding
    intro s t hst
    exact congrArg Prod.fst ((C).injective (D.symm.injective hst))
  have hdis : Pairwise (fun z w : B => Disjoint (range (arc z)) (range (arc w))) := by
    intro z w hzw
    apply disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, heq⟩
    exact hzw (Subtype.ext (congrArg Prod.snd ((C).injective (D.symm.injective heq))).symm)
  have hwhole : (⋃ z : B, range (arc z)) = {x | (c x).2 = xi} := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, t, rfl⟩ := mem_iUnion.mp hx
      change (c (arc z t)).2 = xi
      rw [hformula]
      change g ((C).symm (D (D.symm ((C) (t, z))))).2 = xi
      rw [D.apply_symm_apply, Homeomorph.symm_apply_apply]
      exact z.property
    · intro hx
      let z : B := ⟨((C).symm (D x)).2, (hformula x).symm.trans hx⟩
      refine mem_iUnion.mpr ⟨z, ((C).symm (D x)).1, ?_⟩
      change D.symm ((C) ((C).symm (D x))) = x
      rw [Homeomorph.apply_symm_apply, D.symm_apply_apply]
  have hmark (z : B) (t : unitInterval) : arc z t ∈ annulusRims ↔ t = 0 ∨ t = 1 := by
    change D.symm ((C) (t, z)) ∈ annulusRims ↔ _
    rw [finitePL_annulus_mem_rims_iff D.symm hD.symm, annulusCylinderHomeomorph_mem_rims]
  let e := Fintype.equivFin B
  refine ⟨Fintype.card B, fun i => arc (e.symm i), fun i => a (e.symm i),
    fun i => hi _, fun i => ha _, fun i => hav _,
    fun i k hik => hdis (fun h => hik (e.symm.injective h)), ?_, fun i => hmark _⟩
  rw [← hwhole]
  apply le_antisymm
  · exact iUnion_mono' (fun i => ⟨e.symm i, subset_rfl⟩)
  · intro x hx
    obtain ⟨z, hz⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨e z, by simpa only [e.symm_apply_apply] using hz⟩

end PoincareConjecture.M76.Dehn

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
local notation "C" => Dehn.annulusCylinderHomeomorph

theorem exists_hamiltonZero_annulus_normal_form_with_coordinates
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {j : ℝ × ℝ → X0} (hj : PolyhedralPLInCharts e j Ann)
    {theta : C0} {cut alpha beta : ℝ}
    (hcut : cut < alpha) (hab : alpha < beta) (hbeta : beta < cut + p)
    (hphase : ∀ z : Ann, (Q0 (hamiltonZeroAmbientMap phi (j z))).1.2 = theta)
    (f : C(Ann, unitInterval × C0)) (label : Bool → Bool)
    (hf : ∀ z : Ann, (f z).2 = (Q0 (hamiltonZeroAmbientMap phi (j z))).1.1)
    (hnormal : ∀ z : Ann, (((beta - alpha) * ((f z).1 : ℝ) + alpha : ℝ) : C0) =
      (Q0 (hamiltonZeroAmbientMap phi (j z))).2)
    (hlabels : ∀ side z, (f (Dehn.annulusRimPoint side z)).1 =
      if label side then 1 else 0)
    (g : C(Circle, C0))
    (hg : ∀ z, g z = (Q0 (hamiltonZeroAmbientMap phi
      (j (Dehn.annulusRimPoint false z)))).1.1)
    (hgc : IsCoveringMap g) (Hrim : Circle ≃ₜ Circle)
    (L : (ContinuousMap.id Circle).Homotopy (Hrim : C(Circle, Circle)))
    (hlift : ∀ t z, g (L (t, z)) = (f ((C) (t, z))).2) :
    let u : C(Ann, X0) := ⟨fun z => hamiltonZeroAmbientMap phi (j z),
      (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩
    ∃ delta0 ∈ ({alpha, beta} : Set ℝ), ∃ delta1 ∈ ({alpha, beta} : Set ℝ),
      ∃ c : C(Ann, unitInterval × C0), IsCoveringMap c ∧
        ∃ q : ℝ × ℝ → X0, PolyhedralPLInCharts d q Ann ∧
          (∀ z : Ann, q z = hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z)) ∧
          Nonempty (u.HomotopyRel
            ((hamiltonZeroAnnulusTargetMap delta0 delta1 theta).comp c) Dehn.annulusRims) ∧
          ∃ D : Ann ≃ₜ Ann, D.IsFinitePL ∧
            ∀ z : Ann, (c z).2 = g ((C).symm (D z)).2 := by
  intro u
  have hrim (side : Bool) (z : Circle) :
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint side z)))).2 =
        ((if label side then beta else alpha : ℝ) : C0) := by
    rw [← hnormal, hlabels]
    cases label side <;> simp
  have hcover : IsCoveringMap (fun z : Circle =>
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z)))).1.1) := by
    convert hgc using 1
    funext z
    exact (hg z).symm
  have hupper (z : Circle) :
      (Q0 (hamiltonZeroAmbientMap phi
        (j (Dehn.annulusRimPoint false (Hrim z))))).1.1 =
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint true z)))).1.1 := by
    have h := hlift 1 z
    rw [L.apply_one, Dehn.annulusCylinderHomeomorph_one, hg, hf] at h
    exact h
  obtain ⟨A, hA, hA0, hA1⟩ := exists_hamiltonZero_source_annulus_rim_extension
    hd hphi hj hphase (hrim false) hcover Hrim L hupper
  by_cases hsame : label false = label true
  · let delta : ℝ := if label false then beta else alpha
    have hdelta : delta ∈ ({alpha, beta} : Set ℝ) := by
      dsimp [delta]
      cases label false <;> simp
    let f' : C(Ann, unitInterval × C0) :=
      ⟨fun z => (((C).symm z).1, (f z).2), by fun_prop⟩
    have hlabels' (side : Bool) (z : Circle) :
        (f' (Dehn.annulusRimPoint side z)).1 = if side then 1 else 0 := by
      cases side
      · change ((C).symm (Dehn.annulusRimPoint false z)).1 = 0
        rw [← Dehn.annulusCylinderHomeomorph_zero, Homeomorph.symm_apply_apply]
      · change ((C).symm (Dehn.annulusRimPoint true z)).1 = 1
        rw [← Dehn.annulusCylinderHomeomorph_one, Homeomorph.symm_apply_apply]
    obtain ⟨D, hD, c, hc, hcf, ⟨Hc⟩⟩ :=
      Dehn.exists_relative_annulus_covering_of_rim_extension f' g hgc Hrim L hlift
        hlabels' A hA hA0 hA1
    obtain ⟨q, hq, hqval⟩ := exists_hamiltonZero_marked_annulus_covering_PL
      (alpha := delta) (beta := delta) hd hphi hj (fun z => hphase _) (hrim false) D hD
    have hqtarget (z : Ann) : q z = hamiltonZeroAnnulusTargetMap delta delta theta (c z) := by
      rw [hqval, hcf]
      simp only [hamiltonZeroAnnulusTargetMap, ContinuousMap.coe_mk, hg]
    have hstart : (hamiltonZeroAnnulusTargetMap delta delta theta).comp f' =
        (hamiltonZeroTargetPhaseRetraction delta).comp u := by
      apply ContinuousMap.ext
      intro z
      apply (Q0).injective
      rw [ContinuousMap.comp_apply, hamiltonZeroAnnulusTargetMap_coordinates,
        ContinuousMap.comp_apply, hamiltonZeroTargetPhaseRetraction_coordinates]
      change (((f z).2, theta), (((delta - delta) * _ + delta : ℝ) : C0)) =
        ((Q0 (hamiltonZeroAmbientMap phi (j z))).1, (delta : C0))
      simp only [sub_self, zero_mul, zero_add]
      exact Prod.ext (Prod.ext (hf z) (hphase z).symm) rfl
    have hdeltaArc : delta ∈ Icc alpha beta := by
      rcases hdelta with h | h <;> rw [h] <;> exact ⟨by linarith, by linarith⟩
    have hslab (z : Ann) : (Q0 (u z)).2 ∈ AddCircle.closedIntervalArc p alpha beta := by
      change (Q0 (hamiltonZeroAmbientMap phi (j z))).2 ∈ _
      rw [← hnormal]
      exact ⟨(beta - alpha) * ((f z).1 : ℝ) + alpha,
        ⟨by nlinarith [(f z).1.property.1], by nlinarith [(f z).1.property.2]⟩, rfl⟩
    obtain ⟨_, T, _, _, _⟩ := hphi.exists_hamiltonZero_folded_annulus_contraction
      hd hcut hbeta hdeltaArc j hj hslab (fun side z => by
        rw [hrim]
        have hlabel : label side = label false := by cases side; rfl; exact hsame.symm
        rw [hlabel])
    refine ⟨delta, hdelta, delta, hdelta, c, hc, q, hq, hqtarget,
      ⟨T.trans ((hamiltonZeroAnnulusCoordinateHomotopy Hc theta delta delta).cast hstart rfl)⟩,
      D, hD, ?_⟩
    intro z
    rw [hcf]
  · obtain ⟨D, hD, c, hc, hcf, ⟨Hc⟩⟩ :=
      Dehn.exists_relative_annulus_covering_of_opposite_rims f g hgc Hrim L hlift
        label hsame hlabels A hA hA0 hA1
    obtain ⟨q, hq, hqval⟩ := exists_hamiltonZero_oriented_marked_annulus_covering_PL
      hd hphi hj (label false) (fun z => hphase _) (hrim false) D hD
    have hqtarget (z : Ann) : q z = hamiltonZeroAnnulusTargetMap alpha beta theta (c z) := by
      rw [hqval, hcf]
      simp only [hamiltonZeroAnnulusTargetMap, ContinuousMap.coe_mk,
        Dehn.annulusTargetReflection, Homeomorph.prodCongr, hg]
      cases label false <;> rfl
    have hstart : (hamiltonZeroAnnulusTargetMap alpha beta theta).comp f = u := by
      apply ContinuousMap.ext
      intro z
      apply (Q0).injective
      rw [ContinuousMap.comp_apply, hamiltonZeroAnnulusTargetMap_coordinates]
      exact Prod.ext (Prod.ext (hf z) (hphase z).symm) (hnormal z)
    refine ⟨alpha, by simp, beta, by simp, c, hc, q, hq, hqtarget,
      ⟨(hamiltonZeroAnnulusCoordinateHomotopy Hc theta alpha beta).cast hstart rfl⟩,
      D, hD, ?_⟩
    intro z
    rw [hcf]
    rfl

theorem exists_hamiltonZero_source_annulus_normal_form_with_PL_arcs
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi psi : C(H0, H0))
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
    {R A : Set X0} (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {theta other : C0} (hne : theta ≠ other)
    (hreg : HamiltonZeroSecondCoordinateRegularity e R phi theta)
    {a b : ℝ}
    (hN : PLDomain e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) ∪
          (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {other})))
    (hcover : IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta))
    {S : Set X0} (hS : S ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta})
    (hcomponent : ∀ x ∈ S, connectedComponentIn
      (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) x = S)
    (H : Ann ≃ₜ S) (j : ℝ × ℝ → X0) (hj : PolyhedralPLInCharts e j Ann)
    (hJ : ∀ z : Ann, j z = (H z : X0))
    (hmark : ∀ z : Ann, depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
      (H z : X0) ∈ frontier R)
    {cut alpha beta : ℝ} (halpha : cut < alpha) (halphabeta : alpha < beta)
    (hbeta : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap psi ⁻¹' {(alpha : C0), (beta : C0)}) :
    let u : C(Ann, X0) := ⟨fun z => hamiltonZeroAmbientMap psi (j z),
      (hamiltonZeroAmbientMap psi).continuous.comp hj.continuousOn.domRestrict⟩
    ∃ delta0 ∈ ({alpha, beta} : Set ℝ), ∃ delta1 ∈ ({alpha, beta} : Set ℝ),
      ∃ c : C(Ann, unitInterval × C0), IsCoveringMap c ∧
        ∃ q : ℝ × ℝ → X0, PolyhedralPLInCharts d q Ann ∧
          (∀ z : Ann, q z = hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z)) ∧
          Nonempty (u.HomotopyRel
            ((hamiltonZeroAnnulusTargetMap delta0 delta1 theta).comp c) Dehn.annulusRims) ∧
          ∀ xi : C0, ∃ (n : ℕ) (arc : Fin n → C(unitInterval, Ann))
              (param : Fin n → ℝ → ℝ × ℝ),
            (∀ i, Topology.IsEmbedding (arc i)) ∧
            (∀ i, FinitePiecewiseAffineOn (param i) (Icc (0 : ℝ) 1)) ∧
            (∀ i (t : unitInterval), param i t = (arc i t : ℝ × ℝ)) ∧
            (∀ i, PolyhedralPLInCharts e (j ∘ param i) (Icc (0 : ℝ) 1)) ∧
            Pairwise (fun i k => Disjoint (range (arc i)) (range (arc k))) ∧
            (⋃ i, range (arc i)) = {z | (c z).2 = xi} ∧
            ∀ i t, j (arc i t) ∈ frontier R ↔ t = 0 ∨ t = 1 := by
  intro u
  obtain ⟨f, label, g, hf, hnormal, hlabels, hg, hgc, _, Hrim, L, hlift⟩ :=
    exists_hamiltonZero_source_annulus_rim_lift e phi psi heR hA hAR hfixed hne hreg
      hN hfront hcover hS hcomponent H hmark halpha halphabeta hbeta hR hRfront
  have hphase (z : Ann) : (Q0 (hamiltonZeroAmbientMap psi (j z))).1.2 = theta := by
    rw [hJ, ← hamiltonZeroSecondCircleMap_ambient]
    exact (hS (H z).property).2
  have hf' (z : Ann) : (f z).2 = (Q0 (hamiltonZeroAmbientMap psi (j z))).1.1 := by
    rw [hJ]
    exact hf z
  have hn' (z : Ann) : (((beta - alpha) * ((f z).1 : ℝ) + alpha : ℝ) : C0) =
      (Q0 (hamiltonZeroAmbientMap psi (j z))).2 := by
    rw [hJ]
    exact hnormal z
  have hg' (z : Circle) : g z =
      (Q0 (hamiltonZeroAmbientMap psi (j (Dehn.annulusRimPoint false z)))).1.1 := by
    rw [hJ]
    exact hg z
  obtain ⟨delta0, hd0, delta1, hd1, c, hc, q, hq, hqval, hhom, D, hD, hcf⟩ :=
    exists_hamiltonZero_annulus_normal_form_with_coordinates hd hpsi hj halpha halphabeta hbeta
      hphase f label hf' hn' (fun side z => congrArg Prod.fst (hlabels side z))
      g hg' hgc Hrim L hlift
  refine ⟨delta0, hd0, delta1, hd1, c, hc, q, hq, hqval, hhom, ?_⟩
  intro xi
  obtain ⟨n, arc, param, hi, hPL, hparam, hdis, hwhole, hends⟩ :=
    Dehn.exists_marked_finitePL_vertical_arc_family D hD g hgc c hcf xi
  refine ⟨n, arc, param, hi, hPL, hparam, ?_, hdis, hwhole, ?_⟩
  · intro i
    obtain ⟨K, hK, hKs, _⟩ := hPL i
    have hmap : MapsTo (param i) K.space Ann := by
      intro t ht
      rw [hparam i ⟨t, hKs.subset ht⟩]
      exact (arc i ⟨t, hKs.subset ht⟩).property
    have h := hj.comp_finitePiecewiseAffineOn K hK
      (show FinitePiecewiseAffineOn (param i) K.space from hKs.symm ▸ hPL i) hmap
    simpa only [hKs] using h
  · intro i t
    rw [hJ, ← hmark]
    have hrim : arc i t ∈ Dehn.annulusRims ↔
        depth 8 (arc i t : ℝ × ℝ) = -1 ∨ depth 8 (arc i t : ℝ × ℝ) = 1 := by
      rw [Dehn.annulusRims, mem_union, Dehn.range_annulusRimPoint, Dehn.range_annulusRimPoint]
      rfl
    exact hrim.symm.trans (hends i t)

end PoincareConjecture.M76
