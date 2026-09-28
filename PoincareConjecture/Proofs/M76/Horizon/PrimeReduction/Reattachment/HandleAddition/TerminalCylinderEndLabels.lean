import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcCoordinates


set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_annular_endpoint_labels
    {ι κ α Y : Type*} [Fintype ι] [Fintype κ]
    [TopologicalSpace Y] [ConnectedSpace Y] [Nonempty Y]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ (W : (Y × J) ≃ₜ ↥(E ∩ D))
      (_hends : ∀ z, (W z : X) ∈ frontier R ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1),
      ∃ a : Bool → sphere (0 : ι → ℝ) 1, Function.Bijective a ∧
        ∀ side y, (W (y,⟨if side then 1 else -1,by cases side <;> norm_num⟩) : X).1 = a side := by
  classical
  intro X R E W hends
  obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hi
  let : Unique ι := hu
  let : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  let S := sphere (0 : ι → ℝ) 1
  have hSf : S.Finite := by
    apply ((Set.finite_singleton (fun _ : ι => (-1 : ℝ))).insert (fun _ : ι => (1 : ℝ))).subset
    intro x hx
    have hc : x = (fun _ => x default) := funext (fun i => congrArg x (Subsingleton.elim i default))
    have hn : |x default| = 1 := by
      have hh := mem_sphere_zero_iff_norm.mp hx
      rwa [hc,pi_norm_const,Real.norm_eq_abs] at hh
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with hn | hn
    · exact Or.inl (hc.trans (by rw [hn]))
    · exact Or.inr (hc.trans (by rw [hn]))
  let : Finite S := hSf.to_subtype
  let : DiscreteTopology S := inferInstance
  let t (side : Bool) : J := ⟨if side then 1 else -1,by cases side <;> norm_num⟩
  have hfront (side : Bool) (y : Y) : (W (y,t side) : X) ∈ frontier R := by
    apply (hends _).mpr
    cases side <;> simp [t]
  have hfirst (side : Bool) (y : Y) : (W (y,t side) : X).1 ∈ S := by
    have hh := hfront side y
    change (W (y,t side) : X) ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ
      (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup))) at hh
    rw [frontier_prod_univ_eq,frontier_closedBall _ one_ne_zero] at hh
    exact hh.1
  let first (side : Bool) : C(Y,S) := ⟨fun y => ⟨(W (y,t side) : X).1,hfirst side y⟩,
    (continuous_fst.comp (continuous_subtype_val.comp
      (W.continuous.comp (continuous_id.prodMk continuous_const)))).subtype_mk _⟩
  let a (side : Bool) : S := first side (Classical.choice ‹Nonempty Y›)
  have ha (side : Bool) (y : Y) : first side y = a side :=
    (isPreconnected_range (first side).continuous).subsingleton (mem_range_self y)
      (mem_range_self (Classical.choice ‹Nonempty Y›))
  have hmark : D ∩ frontier R = hamiltonAttachingBlock ι κ L (3/2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hcontact := b.closed_complement_lateral_contact he hdim hi
  have hsur : Function.Surjective a := by
    intro v
    let z : κ → ℝ := fun _ => 3/2
    have hz : z ∈ sphere (0 : κ → ℝ) (3/2) := by simp [z,pi_norm_const]
    let x : X := (v,(QuotientAddGroup.mk z : (κ → ℝ) ⧸ L.toAddSubgroup))
    have hrim : x ∈ hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3/2)) :=
      ⟨(v,z),⟨v.property,hz⟩,rfl⟩
    have hxatt := image_mono (prod_mono subset_rfl sphere_subset_closedBall) hrim
    have hxD := (hmark.symm.subset hxatt).1
    have hxf := (hmark.symm.subset hxatt).2
    have hxfront := ((b.ball.frontier_inter_eq_of_subset b.subset_domain).symm.subset
      ⟨hxD,hxf⟩).1
    have hxT : x ∈ E ∩ D := hcontact.symm.subset ⟨hxfront,fun h => h.2 hrim⟩
    obtain ⟨w,hw⟩ := W.surjective ⟨x,hxT⟩
    have hwold : (W w : X) ∈ frontier R := (congrArg Subtype.val hw).symm ▸ hxf
    rcases (hends w).mp hwold with hwm | hwp
    · have hwt : w = (w.1,t false) := Prod.ext rfl (Subtype.ext hwm)
      refine ⟨false,?_⟩
      apply Subtype.ext
      have hh := congrArg Subtype.val (ha false w.1)
      change (W (w.1,t false) : X).1 = (a false : ι → ℝ) at hh
      exact hh.symm.trans (congrArg (fun u : ↥(E ∩ D) => (u : X).1) (hwt ▸ hw))
    · have hwt : w = (w.1,t true) := Prod.ext rfl (Subtype.ext hwp)
      refine ⟨true,?_⟩
      apply Subtype.ext
      have hh := congrArg Subtype.val (ha true w.1)
      change (W (w.1,t true) : X).1 = (a true : ι → ℝ) at hh
      exact hh.symm.trans (congrArg (fun u : ↥(E ∩ D) => (u : X).1) (hwt ▸ hw))
  have hne : a false ≠ a true := by
    intro h
    have heq (v : S) : v = a false := by
      obtain ⟨side,rfl⟩ := hsur v
      cases side
      · rfl
      · exact h.symm
    let vminus : S := ⟨fun _ => -1,by simp [S,pi_norm_const]⟩
    let vplus : S := ⟨fun _ => 1,by simp [S,pi_norm_const]⟩
    have hh := congrArg (fun v : S => (v : ι → ℝ) default)
      ((heq vminus).trans (heq vplus).symm)
    norm_num [vminus,vplus] at hh
  refine ⟨a,⟨?_,hsur⟩,fun side y => congrArg Subtype.val (ha side y)⟩
  intro side side' h
  cases side <;> cases side' <;> simp_all

end PoincareConjecture.M76
