import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.SlabInjection

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem hamiltonZero_box_pi1_subsingleton
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {S : Set X0} {cut alpha beta cut' u v cut'' a b : ℝ}
    (halpha : cut < alpha) (hbeta : beta < cut + p)
    (hu : cut' < u) (hv : v < cut' + p)
    (ha : cut'' < a) (hb : b < cut'' + p)
    (hfirst : S ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : S ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v)
    (hthird : S ⊆ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (x : S)
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X0)) x)) :
    Subsingleton (FundamentalGroup S x) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let inc : C(S, X0) := ⟨Subtype.val, continuous_subtype_val⟩
  let ambient : C(X0, H0) := hamiltonZeroAmbientEquiv
  let coords : C(H0, (C0 × C0) × C0) := hamiltonZeroHierarchyCoordinates
  let f := coords.comp (phi.comp (ambient.comp inc))
  have hf : Function.Injective (FundamentalGroup.map f x) := by
    change Function.Injective (FundamentalGroup.map (coords.comp (phi.comp (ambient.comp inc))) x)
    rw [FundamentalGroup.map_comp, FundamentalGroup.map_comp, FundamentalGroup.map_comp]
    exact (hamiltonZeroHierarchyCoordinates.fundamentalGroupMulEquiv
      (phi (ambient (inc x)))).injective.comp
      ((F.fundamentalGroup_map_bijective (ambient (inc x))).1.comp
        ((hamiltonZeroAmbientEquiv.fundamentalGroupMulEquiv (inc x)).injective.comp hinj))
  let J := AddCircle.openPartialHomeomorphCoe p cut
  let K := AddCircle.openPartialHomeomorphCoe p cut'
  let L := AddCircle.openPartialHomeomorphCoe p cut''
  have hJ (y : S) : (f y).2 ∈ J.target := by
    obtain ⟨r, hr, he⟩ := hfirst y.property
    change hamiltonZeroCircleMap phi y ∈ J.target
    rw [← he]
    exact J.map_source ⟨halpha.trans_le hr.1, hr.2.trans_lt hbeta⟩
  have hK (y : S) : (f y).1.2 ∈ K.target := by
    obtain ⟨r, hr, he⟩ := hsecond y.property
    change hamiltonZeroSecondCircleMap phi y ∈ K.target
    rw [← he]
    exact K.map_source ⟨hu.trans_le hr.1, hr.2.trans_lt hv⟩
  have hL (y : S) : (f y).1.1 ∈ L.target := by
    obtain ⟨r, hr, he⟩ := hthird y.property
    change hamiltonZeroThirdCircleMap phi y ∈ L.target
    rw [← he]
    exact L.map_source ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  let lift : C(S, (ℝ × ℝ) × ℝ) :=
    ⟨fun y => ((L.symm (f y).1.1, K.symm (f y).1.2), J.symm (f y).2),
      ((L.continuousOn_symm.comp_continuous f.continuous.fst.fst hL).prodMk
        (K.continuousOn_symm.comp_continuous f.continuous.fst.snd hK)).prodMk
        (J.continuousOn_symm.comp_continuous f.continuous.snd hJ)⟩
  let sectionMap : C((ℝ × ℝ) × ℝ, (C0 × C0) × C0) :=
    ⟨fun z => (((z.1.1 : C0), (z.1.2 : C0)), (z.2 : C0)),
      (((AddCircle.continuous_mk' p).comp continuous_fst.fst).prodMk
        ((AddCircle.continuous_mk' p).comp continuous_fst.snd)).prodMk
        ((AddCircle.continuous_mk' p).comp continuous_snd)⟩
  have hfactor : sectionMap.comp lift = f := by
    apply ContinuousMap.ext
    intro y
    exact Prod.ext (Prod.ext (L.right_inv (hL y)) (K.right_inv (hK y))) (J.right_inv (hJ y))
  rw [← hfactor, FundamentalGroup.map_comp] at hf
  have hg : Function.Injective (FundamentalGroup.map lift x) :=
    Function.Injective.of_comp hf
  exact hg.subsingleton

theorem hamiltonZero_terminal_third_slabs_pi1_subsingleton
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi : C(H0, H0)) (Fpsi : (ContinuousMap.id H0).HomotopyRel psi B0)
    {R A : Set X0} (heR : PLDomain e R)
    (hinjR : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hreg : ∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e R phi (theta : C0))
    (geometry : HamiltonZeroThirdPhaseGeometry e R psi a b)
    (hboundary : (frontier R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)}).Nonempty)
    {cut alpha beta cut' u v : ℝ}
    (halpha : cut < alpha) (hbeta : beta < cut + p)
    (hu : cut' < u) (hv : v < cut' + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p u v) :
    ∀ side : Bool,
      let N := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      ∀ x : N, Subsingleton (FundamentalGroup N x) := by
  have hsides := hamiltonZero_third_slabs_pi1_injective e phi psi heR hA hAR hfixed
    ha hab hb hreg geometry hboundary
  intro side
  dsimp only
  let N := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
    AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
  intro x
  have hi : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(N, X0)) x) := by
    let incl := ContinuousMap.inclusion (inter_subset_left : N ⊆ R)
    let ambient : C(R, X0) := ⟨Subtype.val, continuous_subtype_val⟩
    change Function.Injective (FundamentalGroup.map (ambient.comp incl) x)
    rw [FundamentalGroup.map_comp]
    exact (hinjR (incl x)).comp (hsides side x)
  have hfirstN := (inter_subset_left : N ⊆ R).trans hfirst
  have hsecondN := (inter_subset_left : N ⊆ R).trans hsecond
  cases side
  · exact hamiltonZero_box_pi1_subsingleton psi Fpsi halpha hbeta hu hv
      (cut'' := 0) ha (by change b < 0 + p; linarith) hfirstN hsecondN inter_subset_right x hi
  · exact hamiltonZero_box_pi1_subsingleton psi Fpsi halpha hbeta hu hv
      (cut'' := (a + b) / 2) (by change (a + b) / 2 < b; linarith)
      (by change a + p < (a + b) / 2 + p; linarith) hfirstN hsecondN inter_subset_right x hi

end PoincareConjecture.M76
