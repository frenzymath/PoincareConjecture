import PoincareConjecture.Proofs.M25.AppA_21_Local.CapSecondTubeTail
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapSecondEndTail
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapChainIntersection
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M25

set_option linter.unusedVariables false in

theorem L3_doubleCappedTube_of_disjoint_core_carrier :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : ConnectedNeckCapCover g) (hsmall : H.epsilon ≤ epsilon0)
      (C0 C1 : CapCertificate g) (D : BalancedNeckChain g C0.epsilon) {b : ℤ}
      (hC0 : C0 ∈ H.caps) (hC1 : C1 ∈ H.caps)
      (hshape : D.shape = ChainShape.finite 0 b) (hstart : D.neck 0 = C0.end_neck)
      (hsep : ∀ i ∈ D.shape.active, (D.neck i).IsSeparating)
      (hout : ∀ i ∈ D.shape.active, 0 < i → (D.neck i).center ∉ C0.carrier)
      (hquarters : ∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
        closure ((D.neck i).region (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹) ⊆
            (D.neck (i + 1)).carrier ∧
          closure ((D.neck (i + 1)).region
              (-C0.epsilon⁻¹) (-C0.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier)
      (hno : ¬ (C0.carrier \ C0.end_neck.region
        (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹ ⊆ C1.core))
      (K : CappedTubeCertificate g) (hKcap : K.cap = C0)
      (hKeps : K.tube.epsilon = H.epsilon)
      (hKtube : K.tube.carrier = (⋃ i ∈ D.shape.active, (D.neck i).carrier))
      (hKcarrier : K.carrier = C0.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier))
      (hdisjoint : Disjoint C0.closed_core C1.carrier)
      (y : M) (hycore : y ∈ C1.core)
      (hyclosure : y ∈ closure ((D.neck b).region 0 C0.epsilon⁻¹))
      (hyout : y ∉ K.carrier)
      (hmeet : (K.carrier ∩ C1.boundary_sphere).Nonempty)
      (hcompact : IsCompact (K.carrier ∪ C1.carrier))
      (hconnected : IsConnected (K.carrier ∪ C1.carrier))
      (hcyl : Nonempty (OpenCylinderModel (C1.carrier ∩ K.tube.carrier))),
      ∃ Dc : DoubleCappedTubeCertificate g,
        Dc.cap₁ = C0 ∧ Dc.cap₂ = C1 ∧ Dc.tube.epsilon = H.epsilon ∧
        Dc.carrier = K.carrier ∪ C1.carrier := by
  obtain ⟨epsilon0, hpos, hcap, htails⟩ :=
    CapCertificate.exists_opposite_tube_tail_of_finite_core_frontier.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g H hsmall C0 C1 D b hC0 hC1 hshape hstart hsep
    hout hquarters hno K hKcap hKeps hKtube hKcarrier hdisjoint y hycore
    hyclosure hyout hmeet hcompact hconnected hcyl
  classical
  have hC0e : C0.epsilon = H.epsilon := H.cap_epsilon C0 hC0
  have hC1e : C1.epsilon = H.epsilon := H.cap_epsilon C1 hC1
  have hsmall0 : C0.epsilon ≤ epsilon0 := hC0e.trans_le hsmall
  have hepsilon : C1.epsilon = C0.epsilon := hC1e.trans hC0e.symm
  have hcore1 : C1.closed_core ⊆ C1.carrier := by
    rw [C1.closed_core_eq_complement_end]
    exact sdiff_subset
  have hcores : Disjoint C0.closed_core C1.closed_core := hdisjoint.mono_right hcore1
  obtain ⟨side, t, a0, a1, _, ha0, ha1, htail0, htail1, ⟨A0⟩⟩ :=
    htails C0 C1 D hsmall0 hepsilon hshape hstart hsep hout hquarters hno
      K hKcap hKtube hcores y hycore hyclosure hyout hmeet
  have hb : (0 : ℤ) ≤ b := by
    obtain ⟨i, hi⟩ := D.active_nonempty
    rw [hshape] at hi
    exact hi.1.trans hi.2
  have hzero : (0 : ℤ) ∈ D.shape.active := by
    rw [hshape]
    exact ⟨le_rfl, hb⟩
  have hfirst : ∀ i ∈ D.shape.active, (0 : ℤ) ≤ i := by
    intro i hi
    rw [hshape] at hi
    exact hi.1
  have hinter : C0.carrier ∩ K.tube.carrier = C0.end_neck.carrier := by
    rw [hKtube]
    exact C0.inter_chain_union_eq_end_neck D hzero hfirst hstart hout
  have hinterK : K.cap.carrier ∩ K.tube.carrier = K.cap.end_neck.carrier := by
    simpa only [hKcap] using hinter
  have hdisjointK : Disjoint K.cap.closed_core C1.carrier := by
    simpa only [hKcap] using hdisjoint
  obtain ⟨_, _, _, hend⟩ :=
    C1.exists_second_end_tail_of_compact_extension K hinterK hdisjointK hcompact
  have hL1 : 0 < C1.epsilon⁻¹ := inv_pos.mpr C1.epsilon_pos
  obtain ⟨s, hs, _, hsTail⟩ := hend 0 ⟨neg_lt_zero.mpr hL1, hL1⟩
  have hs' : s ∈ Ioo 0 C1.epsilon⁻¹ := by simpa only [max_self] using hs
  obtain ⟨Z1⟩ := hcyl
  let A1 : CapTubeAttachment C1 K.tube (!side) :=
    { overlap_model := Z1
      tube_tail := ⟨a1, ha1, htail1⟩
      cap_tail := ⟨s, hs', hsTail⟩ }
  have pack (T : EpsilonTubeCertificate g (∅ : Set M))
      (hT : T.carrier = K.tube.carrier) (heT : T.epsilon = H.epsilon)
      (first : CapTubeAttachment C0 T false) (second : CapTubeAttachment C1 T true) :
      ∃ Dc : DoubleCappedTubeCertificate g,
        Dc.cap₁ = C0 ∧ Dc.cap₂ = C1 ∧ Dc.tube.epsilon = H.epsilon ∧
        Dc.carrier = K.carrier ∪ C1.carrier := by
    let Dc : DoubleCappedTubeCertificate g :=
      { carrier := K.carrier ∪ C1.carrier
        cap₁ := C0
        cap₂ := C1
        tube := T
        cap₁_subset := by
          intro x hx
          apply Or.inl
          apply K.cap_subset
          simpa only [hKcap] using hx
        cap₂_subset := fun _ hx => Or.inr hx
        tube_subset := by
          intro x hx
          exact Or.inl (K.tube_subset (hT ▸ hx))
        carrier_eq_union := by
          rw [hT, hKcarrier, hKtube]
        disjoint_cores := hcores
        connected := hconnected
        compact := hcompact
        first_attachment := first
        second_attachment := second }
    exact ⟨Dc, rfl, rfl, heT, rfl⟩
  cases side with
  | false =>
    exact pack K.tube rfl hKeps A0 A1
  | true =>
    let Z := K.tube.cylinder
    let rho : RoundCylinderSpace → RoundCylinderSpace := fun z => (z.1, 1 - z.2)
    have hrho (z : RoundCylinderSpace) : rho (rho z) = z := by
      apply Prod.ext
      · rfl
      · change 1 - (1 - z.2) = z.2
        ring
    have hrho_mem (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
        rho z ∈ univ ×ˢ Ioo (0 : ℝ) 1 := by
      refine ⟨mem_univ _, ?_⟩
      change 0 < 1 - z.2 ∧ 1 - z.2 < 1
      constructor <;> linarith only [hz.2.1, hz.2.2]
    have hrho_smooth : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ rho :=
      contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
    let flip : Ioo (0 : ℝ) 1 → Ioo (0 : ℝ) 1 := fun r =>
      ⟨1 - r.1, by constructor <;> linarith only [r.property.1, r.property.2]⟩
    have hflip (r : Ioo (0 : ℝ) 1) : flip (flip r) = r := by
      apply Subtype.ext
      change 1 - (1 - (r : ℝ)) = (r : ℝ)
      ring
    have hflip_cont : Continuous flip := by
      exact (continuous_const.sub continuous_subtype_val).subtype_mk _
    let rhoI : (UnitTwoSphere × Ioo (0 : ℝ) 1) ≃ₜ
        (UnitTwoSphere × Ioo (0 : ℝ) 1) :=
      { toFun := fun z => (z.1, flip z.2)
        invFun := fun z => (z.1, flip z.2)
        left_inv := fun z => Prod.ext rfl (hflip z.2)
        right_inv := fun z => Prod.ext rfl (hflip z.2)
        continuous_toFun := continuous_fst.prodMk (hflip_cont.comp continuous_snd)
        continuous_invFun := continuous_fst.prodMk (hflip_cont.comp continuous_snd) }
    let Zr : OpenCylinderModel K.tube.carrier :=
      { homeomorph := rhoI.trans Z.homeomorph
        coordinate := fun z => Z.coordinate (rho z)
        coordinate_eq := by
          intro z
          change (Z.homeomorph (rhoI z) : M) = Z.coordinate (rho (z.1, (z.2 : ℝ)))
          exact Z.coordinate_eq (rhoI z)
        coordinate_smooth := Z.coordinate_smooth.comp hrho_smooth.contMDiffOn
          (fun z hz => hrho_mem z hz)
        inverse := fun x => rho (Z.inverse x)
        inverse_mem := fun x hx => hrho_mem (Z.inverse x) (Z.inverse_mem x hx)
        left_inverse := by
          intro z hz
          change rho (Z.inverse (Z.coordinate (rho z))) = z
          rw [Z.left_inverse (hrho_mem z hz)]
          exact hrho z
        right_inverse := by
          intro x hx
          change Z.coordinate (rho (rho (Z.inverse x))) = x
          rw [hrho]
          exact Z.right_inverse hx
        inverse_smooth := hrho_smooth.comp_contMDiffOn Z.inverse_smooth }
    have htail_false (a : ℝ) : Zr.tail false (1 - a) = Z.tail true a := by
      change (fun z => Z.coordinate (rho z)) '' (univ ×ˢ Ioo (0 : ℝ) (1 - a)) =
        Z.coordinate '' (univ ×ˢ Ioo a 1)
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨rho z, ⟨mem_univ _, ?_⟩, rfl⟩
        change a < 1 - z.2 ∧ 1 - z.2 < 1
        constructor <;> linarith only [hz.2.1, hz.2.2]
      · rintro ⟨z, hz, rfl⟩
        refine ⟨rho z, ⟨mem_univ _, ?_⟩, ?_⟩
        · change 0 < 1 - z.2 ∧ 1 - z.2 < 1 - a
          constructor <;> linarith only [hz.2.1, hz.2.2]
        · change Z.coordinate (rho (rho z)) = Z.coordinate z
          rw [hrho]
    have htail_true (a : ℝ) : Zr.tail true (1 - a) = Z.tail false a := by
      change (fun z => Z.coordinate (rho z)) '' (univ ×ˢ Ioo (1 - a) (1 : ℝ)) =
        Z.coordinate '' (univ ×ˢ Ioo 0 a)
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨rho z, ⟨mem_univ _, ?_⟩, rfl⟩
        change 0 < 1 - z.2 ∧ 1 - z.2 < a
        constructor <;> linarith only [hz.2.1, hz.2.2]
      · rintro ⟨z, hz, rfl⟩
        refine ⟨rho z, ⟨mem_univ _, ?_⟩, ?_⟩
        · change 1 - a < 1 - z.2 ∧ 1 - z.2 < 1
          constructor <;> linarith only [hz.2.1, hz.2.2]
        · change Z.coordinate (rho (rho z)) = Z.coordinate z
          rw [hrho]
    have hmiddle : Zr.middleSphere = Z.middleSphere := by
      change (fun z => Z.coordinate (rho z)) '' (univ ×ˢ ({1 / 2} : Set ℝ)) =
        Z.coordinate '' (univ ×ˢ ({1 / 2} : Set ℝ))
      ext x
      constructor
      · rintro ⟨⟨q, r⟩, ⟨_, hr⟩, rfl⟩
        have hr' : r = 1 / 2 := hr
        subst r
        refine ⟨(q, 1 / 2), ⟨mem_univ _, rfl⟩, ?_⟩
        norm_num [rho]
      · rintro ⟨⟨q, r⟩, ⟨_, hr⟩, rfl⟩
        have hr' : r = 1 / 2 := hr
        subst r
        refine ⟨(q, 1 / 2), ⟨mem_univ _, rfl⟩, ?_⟩
        norm_num [rho]
    let Tr : EpsilonTubeCertificate g (∅ : Set M) :=
      { epsilon := K.tube.epsilon
        epsilon_pos := K.tube.epsilon_pos
        epsilon_le_threshold := K.tube.epsilon_le_threshold
        carrier := K.tube.carrier
        carrier_open := K.tube.carrier_open
        contains_X := K.tube.contains_X
        chain := K.tube.chain
        carrier_eq_chain_union := K.tube.carrier_eq_chain_union
        cylinder := Zr
        central_sphere_isotopy := by
          intro i hi
          rw [hmiddle]
          exact K.tube.central_sphere_isotopy i hi }
    have ha0r : 1 - a0 ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> linarith only [ha0.1, ha0.2]
    have ha1r : 1 - a1 ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> linarith only [ha1.1, ha1.2]
    let A0r : CapTubeAttachment C0 Tr false :=
      { overlap_model := A0.overlap_model
        tube_tail := by
          refine ⟨1 - a0, ha0r, ?_⟩
          change Zr.tail false (1 - a0) ⊆ C0.carrier
          rw [htail_false]
          intro x hx
          exact C0.end_neck_subset (htail0 hx).1
        cap_tail := A0.cap_tail }
    let A1r : CapTubeAttachment C1 Tr true :=
      { overlap_model := A1.overlap_model
        tube_tail := by
          refine ⟨1 - a1, ha1r, ?_⟩
          change Zr.tail true (1 - a1) ⊆ C1.carrier
          rw [htail_true]
          exact htail1
        cap_tail := A1.cap_tail }
    exact pack Tr rfl hKeps A0r A1r

end PoincareConjecture.M25
