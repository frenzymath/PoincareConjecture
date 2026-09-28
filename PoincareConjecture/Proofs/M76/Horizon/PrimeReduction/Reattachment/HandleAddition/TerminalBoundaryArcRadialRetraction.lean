import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcRadialImage
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcGraphLift
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.EnclosingAnnularCircle

set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "I" => Icc (0 : ℝ) 1

theorem exists_radial_half_cylinder_retraction
    {Y V : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : C(Y,V)) (hvi : Function.Injective v)
    (hvn : ∀ y,‖v y‖ = 3/2) (hvr : range v = sphere (0 : V) (3/2)) :
    ∃ r : C({z : V // 3/4 ≤ ‖z‖},Y × I),
      ∀ (y : Y) (t : I) (hz : 3/4 ≤ ‖(1-(t : ℝ)/2) • v y‖),
        r ⟨(1-(t : ℝ)/2) • v y,hz⟩ = (y,t) := by
  let f : Y → sphere (0 : V) (3/2) := fun y => ⟨v y,mem_sphere_zero_iff_norm.mpr (hvn y)⟩
  have hfc : Continuous f := v.continuous.subtype_mk _
  have hfi : Function.Injective f := fun y z hh => hvi (congrArg Subtype.val hh)
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨y,hy⟩ := hvr.symm.subset z.property
    exact ⟨y,Subtype.ext hy⟩
  let H := hfc.isClosedEmbedding hfi |>.isEmbedding.toHomeomorphOfSurjective hfs
  let A := {z : V // 3/4 ≤ ‖z‖}
  have hne (z : A) : ‖(z : V)‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) z.property)
  let normalize : A → sphere (0 : V) (3/2) := fun z =>
    ⟨((3/2 : ℝ)/‖(z : V)‖) • z,by
      rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (by positivity),div_mul_cancel₀ _ (hne z)]⟩
  have hnormc : Continuous normalize := by
    apply Continuous.subtype_mk
    exact (continuous_const.div (continuous_norm.comp continuous_subtype_val) hne).smul
      continuous_subtype_val
  let height : A → I := fun z => ⟨max 0 (min 1 (2-(4/3 : ℝ)*‖(z : V)‖)),
    le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
  have hheightc : Continuous height := by
    apply Continuous.subtype_mk
    fun_prop
  let r : C(A,Y × I) := ⟨fun z => (H.symm (normalize z),height z),
    (H.symm.continuous.comp hnormc).prodMk hheightc⟩
  refine ⟨r,?_⟩
  intro y t hz
  let z : A := ⟨(1-(t : ℝ)/2) • v y,hz⟩
  have hcoef : 0 < 1-(t : ℝ)/2 := by linarith [t.property.2]
  have hn : ‖(z : V)‖ = (1-(t : ℝ)/2)*(3/2) := by
    change ‖(1-(t : ℝ)/2) • v y‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hcoef,hvn]
  apply Prod.ext
  · change H.symm (normalize z) = y
    apply H.injective
    rw [H.apply_symm_apply]
    apply Subtype.ext
    change ((3/2 : ℝ)/‖(z : V)‖) • ((1-(t : ℝ)/2) • v y) = v y
    rw [smul_smul,hn]
    have hscalar : (3/2 : ℝ)/((1-(t : ℝ)/2)*(3/2))*(1-(t : ℝ)/2) = 1 := by
      field_simp [show (2 : ℝ)-(t : ℝ) ≠ 0 by linarith [t.property.2]]
    rw [hscalar,one_smul]
  · apply Subtype.ext
    change max 0 (min 1 (2-(4/3 : ℝ)*‖(z : V)‖)) = (t : ℝ)
    rw [hn]
    have heq : 2-(4/3 : ℝ)*((1-(t : ℝ)/2)*(3/2)) = (t : ℝ) := by ring
    rw [heq,min_eq_right t.property.2,max_eq_right t.property.1]

theorem nullhomotopic_annular_loop_in_punctured_end_disk
    {X κ : Type*} [TopologicalSpace X] [T2Space X] [Fintype κ]
    (hκ : Fintype.card κ = 2) (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {End B : Set X} (hBE : B ⊆ End)
    (F : C(End,(κ → ℝ) ⧸ L.toAddSubgroup)) (hFi : Function.Injective F)
    (havoid : ∀ x : End,F x ∉ QuotientAddGroup.mk '' ball (0 : κ → ℝ) (3/4))
    (H : (sphere (0 : Fin 2 → ℝ) 1) × I ≃ₜ B)
    (v : C(sphere (0 : Fin 2 → ℝ) 1,κ → ℝ))
    (hvi : Function.Injective v) (hvn : ∀ y,‖v y‖ = 3/2)
    (hFB : ∀ z,F ⟨H z,hBE (H z).property⟩ =
      QuotientAddGroup.mk ((1-(z.2 : ℝ)/2) • v z.1))
    (j : C(closedBall (0 : Fin 2 → ℝ) 1,End)) (hji : Function.Injective j)
    (gamma : C(sphere (0 : Fin 2 → ℝ) 1,B))
    (hgamma : ∀ y, (⟨gamma y,hBE (gamma y).property⟩ : End) ∈ range j) :
    gamma.Nullhomotopic := by
  classical
  let Disk := closedBall (0 : Fin 2 → ℝ) 1
  let Circle := sphere (0 : Fin 2 → ℝ) 1
  let : ContractibleSpace Disk := contractibleSpace_closedBall zero_le_one
  let : LocallyPathConnectedSpace Disk := (convex_closedBall (0 : Fin 2 → ℝ) 1).locallyPathConnectedSpace
  let : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : ConnectedSpace Circle := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [←Module.finrank_eq_rank]; simp) (0 : Fin 2 → ℝ) zero_le_one)
  let J := (j.continuous.isClosedEmbedding hji).isEmbedding.toHomeomorph
  let mark : C(Circle,range j) := ⟨fun y => ⟨⟨gamma y,hBE (gamma y).property⟩,hgamma y⟩,
    ((continuous_subtype_val.comp gamma.continuous).subtype_mk _).subtype_mk _⟩
  let c : C(Circle,Disk) := (⟨J.symm,J.symm.continuous⟩ : C(range j,Disk)).comp mark
  have hc (y : Circle) : j (c y) = ⟨gamma y,hBE (gamma y).property⟩ :=
    congrArg Subtype.val (J.apply_symm_apply (mark y))
  let coord : C(Circle,Circle × I) := (⟨H.symm,H.symm.continuous⟩ : C(B,Circle × I)).comp gamma
  let radial : C(Circle,κ → ℝ) := ⟨fun y => (1-(coord y).2.val/2) • v (coord y).1,
    (continuous_const.sub ((continuous_subtype_val.comp (continuous_snd.comp coord.continuous)).div_const 2)).smul
      (v.continuous.comp (continuous_fst.comp coord.continuous))⟩
  have hradial (y : Circle) : QuotientAddGroup.mk (radial y) = F (j (c y)) := by
    rw [hc]
    have hh := hFB (H.symm (gamma y))
    change QuotientAddGroup.mk ((1-((H.symm (gamma y)).2 : ℝ)/2) •
      v (H.symm (gamma y)).1) = _
    simpa only [H.apply_symm_apply] using hh.symm
  have hp := (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
    DiscreteTopology.isDiscrete).isCoveringMap
  let z0 : Disk := ⟨0,mem_closedBall_self zero_le_one⟩
  obtain ⟨w0,hw0⟩ := QuotientAddGroup.mk_surjective (F (j z0))
  obtain ⟨G,⟨_,hG⟩,_⟩ := hp.existsUnique_continuousMap_lifts (F.comp j) z0 w0 hw0
  have hGi : Function.Injective G := by
    intro x y hh
    apply hji
    apply hFi
    exact (congrFun hG x).symm.trans ((congrArg QuotientAddGroup.mk hh).trans (congrFun hG y))
  obtain ⟨K,_,hK,hmark⟩ := exists_normalized_lattice_lift_on_connected_mark
    L (F.comp j) G hGi (fun x => congrFun hG x) c radial hradial
  have hKn (x : Disk) : 3/4 ≤ ‖K x‖ := by
    by_contra hn
    exact havoid (j x) ⟨K x,mem_ball_zero_iff.mpr (lt_of_not_ge hn),hK x⟩
  obtain ⟨r,hr⟩ := exists_radial_half_cylinder_retraction v hvi hvn
    (range_eq_sphere_of_injective_circle hκ (by norm_num) v hvi hvn)
  let k : C(Disk,{z : κ → ℝ // 3/4 ≤ ‖z‖}) := ⟨fun x => ⟨K x,hKn x⟩,K.continuous.subtype_mk _⟩
  let fill : C(Disk,B) := (⟨H,H.continuous⟩ : C(Circle × I,B)).comp (r.comp k)
  have hfill (y : Circle) : fill (c y) = gamma y := by
    change H (r (k (c y))) = gamma y
    have hval : k (c y) = ⟨radial y,by rw [←hmark y]; exact hKn (c y)⟩ :=
      Subtype.ext (hmark y)
    rw [hval]
    change H (r ⟨(1-(coord y).2.val/2) • v (coord y).1,_⟩) = gamma y
    rw [hr]
    exact H.apply_symm_apply _
  have heq : fill.comp c = gamma := ContinuousMap.ext hfill
  rw [←heq]
  exact ((id_nullhomotopic Disk).comp_right fill).comp_left c

theorem not_enclosing_polygon_in_punctured_end_disk
    {X κ : Type*} [TopologicalSpace X] [T2Space X] [Fintype κ]
    (hκ : Fintype.card κ = 2) (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {End B : Set X} (hBE : B ⊆ End)
    (F : C(End,(κ → ℝ) ⧸ L.toAddSubgroup)) (hFi : Function.Injective F)
    (havoid : ∀ x : End,F x ∉ QuotientAddGroup.mk '' ball (0 : κ → ℝ) (3/4))
    (H : (sphere (0 : Fin 2 → ℝ) 1) × I ≃ₜ B)
    (v : C(sphere (0 : Fin 2 → ℝ) 1,κ → ℝ))
    (hvi : Function.Injective v) (hvn : ∀ y,‖v y‖ = 3/2)
    (hFB : ∀ z,F ⟨H z,hBE (H z).property⟩ =
      QuotientAddGroup.mk ((1-(z.2 : ℝ)/2) • v z.1))
    (j : C(closedBall (0 : Fin 2 → ℝ) 1,End)) (hji : Function.Injective j)
    (p : (ℝ × ℝ) → X)
    (hp : ContinuousOn p (PLAnnularStrip.squareAnnulus 8 1))
    (hpi : InjOn p (PLAnnularStrip.squareAnnulus 8 1))
    (hBAnn : B ⊆ p '' PLAnnularStrip.squareAnnulus 8 1)
    {n : ℕ} (P : Polygon (ℝ × ℝ) (n+3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hdepth : ∀ x ∈ P.boundary ℝ,-1 < PLAnnularStrip.depth 8 x ∧ PLAnnularStrip.depth 8 x < 1)
    (hencl : Dehn.annulusSquare 8 1 ⊆ P.inside)
    (hPB : p '' P.boundary ℝ ⊆ B)
    (hPD : p '' P.boundary ℝ ⊆ (Subtype.val : End → X) '' range j) : False := by
  classical
  let Ann := PLAnnularStrip.squareAnnulus 8 1
  let Circle := sphere (0 : Fin 2 → ℝ) 1
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : CompactSpace Ann := Dehn.annulusCylinderHomeomorph.compactSpace
  let f : Ann → X := fun z => p z
  have hfc : Continuous f := hp.domRestrict
  have hfi : Function.Injective f := fun x y hh => Subtype.ext (hpi x.property y.property hh)
  let Q := (hfc.isClosedEmbedding hfi).isEmbedding.toHomeomorph
  have hBrange (x : B) : (x : X) ∈ range f := by
    obtain ⟨z,hz,hzx⟩ := hBAnn x.property
    exact ⟨⟨z,hz⟩,hzx⟩
  let back : C(B,Ann) := (⟨Q.symm,Q.symm.continuous⟩ : C(range f,Ann)).comp
    ⟨fun x => ⟨x,hBrange x⟩,continuous_subtype_val.subtype_mk _⟩
  have hback (x : B) : p (back x) = x := congrArg Subtype.val (Q.apply_symm_apply _)
  obtain ⟨gamma,a,hgi,ha,haval,hgd,hgr,hgm,hessential⟩ :=
    exists_essential_enclosing_annular_circle P hP hPi hdepth hencl
  have hgp (y : Circle) : p (gamma y) ∈ p '' P.boundary ℝ :=
    ⟨gamma y,(hgm _).mp (mem_range_self y),rfl⟩
  let g : C(Circle,B) := ⟨fun y => ⟨p (gamma y),hPB (hgp y)⟩,
    (hp.comp_continuous (continuous_subtype_val.comp gamma.continuous)
      (fun y => (gamma y).property)).subtype_mk _⟩
  have hgin (y : Circle) : (⟨g y,hBE (g y).property⟩ : End) ∈ range j := by
    obtain ⟨z,⟨w,hw⟩,hz⟩ := hPD (hgp y)
    exact ⟨w,Subtype.ext ((congrArg Subtype.val hw).trans hz)⟩
  have hnull := nullhomotopic_annular_loop_in_punctured_end_disk hκ L hBE
    F hFi havoid H v hvi hvn hFB j hji g hgin
  have heq : back.comp g = gamma := by
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    exact hpi (back (g y)).property (gamma y).property (hback (g y))
  have hnullgamma : gamma.Nullhomotopic := heq ▸ hnull.comp_right back
  exact hessential (Path.Homotopic.Quotient.eq.mpr
    (Path.Homotopic.map_nullhomotopic_of_nullhomotopic hnullgamma Dehn.squareRimLoop))

end PoincareConjecture.M76
