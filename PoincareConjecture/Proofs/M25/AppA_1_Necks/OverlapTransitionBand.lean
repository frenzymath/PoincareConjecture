import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseGraphComplement
import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseTransitionBand
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}




theorem positive_fiberwise_transition_band_of_overlap_bounds
    (N N' : EpsilonNeck g)
    (hquarter : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier)
    (hoverlap : N.carrier ∩ N'.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        N'.region (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2))
    (e e' : OpenPartialHomeomorph RoundCylinderSpace M)
    (A : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    (hesource : e.source = N.cylinderDomain)
    (hetarget : e.target = N.carrier)
    (he'source : e'.source = N'.cylinderDomain)
    (he'target : e'.target = N'.carrier)
    (he : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e
      N.cylinderDomain)
    (hei : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm
      N.carrier)
    (he' : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e'
      N'.cylinderDomain)
    (he'i : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e'.symm
      N'.carrier)
    (heheight : ∀ z ∈ N.cylinderDomain,
      (N.coordinate_inverse (e z)).2 = z.2)
    (he'height : ∀ z ∈ N'.cylinderDomain,
      (N'.coordinate_inverse (e' z)).2 = z.2)
    {a b : ℝ} (ha : N.epsilon⁻¹ / 2 < a) (hab : a < b)
    (hb : b < N.epsilon⁻¹)
    (hfirst : ∀ z : RoundCylinderSpace, z.2 ∈ Icc a b →
      (e'.symm (e z)).1 = A z.1) :
    let h : RoundCylinderSpace → ℝ := fun z => (e'.symm (e z)).2
    let T := (e.restr (univ ×ˢ Ioo a b)).trans e'.symm
    (∀ t ∈ Icc a b,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun q : UnitTwoSphere => h (A.symm q, t)) ∧
      (∀ q : UnitTwoSphere,
        h (A.symm q, t) ∈ Ioo (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2)) ∧
      range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) =
        range (fun q : UnitTwoSphere => e' (q, h (A.symm q, t)))) ∧
    (∀ q : UnitTwoSphere, StrictMonoOn (fun s => h (q, s)) (Icc a b)) ∧
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h
      (univ ×ˢ Ioo a b) ∧
    (∀ q : UnitTwoSphere, ∀ s ∈ Ioo a b,
      0 < deriv (fun r : ℝ => h (q, r)) s) ∧
    T.source = univ ×ˢ Ioo a b ∧
    T.target = {z : RoundCylinderSpace |
      h (A.symm z.1, a) < z.2 ∧ z.2 < h (A.symm z.1, b)} ∧
    T.target ⊆ N'.cylinderDomain ∧
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ T T.source ∧
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ T.symm T.target ∧
    (∀ z ∈ T.source, T z = (A z.1, h z) ∧ e' (T z) = e z) ∧
    (∀ z ∈ T.target, T.symm z = e.symm (e' z) ∧
      (T.symm z).1 = A.symm z.1 ∧ e (T.symm z) = e' z) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let h : RoundCylinderSpace → ℝ := fun z => (e'.symm (e z)).2
  let T := (e.restr (univ ×ˢ Ioo a b)).trans e'.symm
  let U := (e.trans e'.symm).source
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hL' : 0 < N'.epsilon⁻¹ := inv_pos.mpr N'.epsilon_pos
  have hretained {t : ℝ} (ht : t ∈ Icc a b) :
      t ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ :=
    ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hdom {z : RoundCylinderSpace} (hz : z.2 ∈ Icc a b) : z ∈ N.cylinderDomain :=
    ⟨mem_univ _, by linarith [(hretained hz).1], (hretained hz).2⟩
  have heold {z : RoundCylinderSpace} (hz : z.2 ∈ Icc a b) : e z ∈ N.carrier :=
    hetarget ▸ e.map_source (hesource.symm ▸ hdom hz)
  have henew {z : RoundCylinderSpace} (hz : z.2 ∈ Icc a b) : e z ∈ N'.carrier := by
    apply hquarter
    refine ⟨heold hz, ?_⟩
    rw [heheight z (hdom hz)]
    exact hretained hz
  have hclosedU {z : RoundCylinderSpace} (hz : z.2 ∈ Icc a b) : z ∈ U := by
    change z ∈ e.source ∧ e z ∈ e'.target
    exact ⟨hesource.symm ▸ hdom hz, he'target.symm ▸ henew hz⟩
  have hcoord : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (fun z => e'.symm (e z)) U :=
    he'i.comp (he.mono (fun _ hz => hesource ▸ hz.1))
      (fun _ hz => he'target ▸ hz.2)
  have hhU : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U :=
    contMDiff_snd.comp_contMDiffOn hcoord
  have hh : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h
      (univ ×ˢ Ioo a b) :=
    hhU.mono (fun _ hz => hclosedU ⟨hz.2.1.le, hz.2.2.le⟩)
  have hpair (z : RoundCylinderSpace) (hz : z.2 ∈ Icc a b) :
      e'.symm (e z) = (A z.1, h z) := Prod.ext (hfirst z hz) rfl
  have hpairDom (z : RoundCylinderSpace) (hz : z.2 ∈ Icc a b) :
      (A z.1, h z) ∈ N'.cylinderDomain := by
    rw [← hpair z hz]
    exact he'source ▸ e'.map_target (he'target.symm ▸ henew hz)
  have hforward (z : RoundCylinderSpace) (hz : z.2 ∈ Icc a b) :
      e' (A z.1, h z) = e z := by
    rw [← hpair z hz]
    exact e'.right_inv (he'target.symm ▸ henew hz)
  have hbound (z : RoundCylinderSpace) (hz : z.2 ∈ Icc a b) :
      h z ∈ Ioo (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2) := by
    have hn := (hoverlap ⟨heold hz, henew hz⟩).2.2.2
    have hheight := he'height _ (hpairDom z hz)
    rw [hforward z hz] at hheight
    exact ⟨(hpairDom z hz).2.1, by simpa only [hheight] using hn⟩
  have hgraph (t : ℝ) (ht : t ∈ Icc a b) :
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
          (fun q : UnitTwoSphere => h (A.symm q, t)) ∧
        (∀ q : UnitTwoSphere,
          h (A.symm q, t) ∈ Ioo (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2)) ∧
        range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) =
          range (fun q : UnitTwoSphere => e' (q, h (A.symm q, t))) := by
    refine ⟨hhU.comp_contMDiff (A.symm.contMDiff.prodMk contMDiff_const)
      (fun _ => hclosedU ht), fun q => hbound (A.symm q, t) ht, ?_⟩
    have ht0 : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := (hdom (z := (A.symm
      (N.coordinate_inverse N.center).1, t)) ht).2
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      let y := N.coordinate_map (q, t)
      have hy : y ∈ N.carrier := N.coordinate_map_mem ⟨mem_univ _, ht0⟩
      have hys : e.symm y ∈ N.cylinderDomain :=
        hesource ▸ e.map_target (hetarget.symm ▸ hy)
      have hyt : (e.symm y).2 = t := by
        have hv := heheight (e.symm y) hys
        rw [e.right_inv (hetarget.symm ▸ hy)] at hv
        exact hv.symm.trans (congrArg Prod.snd (N.coordinate_inverse_map _ ht0))
      refine ⟨A (e.symm y).1, ?_⟩
      change e' (A (e.symm y).1, h (A.symm (A (e.symm y).1), t)) = y
      rw [A.symm_apply_apply]
      rw [hforward ((e.symm y).1, t) ht]
      rw [← hyt]
      exact e.right_inv (hetarget.symm ▸ hy)
    · rintro ⟨q, rfl⟩
      have hform : e' (q, h (A.symm q, t)) = e (A.symm q, t) := by
        simpa only [A.apply_symm_apply] using hforward (A.symm q, t) ht
      change e' (q, h (A.symm q, t)) ∈ range (fun p => N.coordinate_map (p, t))
      rw [hform]
      refine ⟨(N.coordinate_inverse (e (A.symm q, t))).1, ?_⟩
      change N.coordinate_map ((N.coordinate_inverse (e (A.symm q, t))).1, t) = e (A.symm q, t)
      have hheight := heheight (A.symm q, t) (hdom ht)
      dsimp only at hheight
      calc
        N.coordinate_map ((N.coordinate_inverse (e (A.symm q, t))).1, t) =
            N.coordinate_map (N.coordinate_inverse (e (A.symm q, t))) :=
          congrArg N.coordinate_map (Prod.ext rfl hheight.symm)
        _ = e (A.symm q, t) := N.coordinate_map_inverse (heold (z := (A.symm q, t)) ht)
  have hmono : ∀ q : UnitTwoSphere, StrictMonoOn (fun s => h (q, s)) (Icc a b) := by
    intro q s hs t ht hst
    have hsret := hretained hs
    have hs0 : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨by linarith [hsret.1], hsret.2⟩
    let f : UnitTwoSphere → ℝ := fun p => h (A.symm p, s)
    have hgs := hgraph s hs
    have hf : Continuous f := hgs.1.continuous
    have hfbound : ∀ p, f p ∈ Ioo (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2) := hgs.2.1
    have hfdom : ∀ p, f p ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ :=
      fun p => ⟨(hfbound p).1, (hfbound p).2.trans (by linarith)⟩
    let S : Set M := range (fun p : UnitTwoSphere => N.coordinate_map (p, s))
    have hmemS {x : M} : x ∈ S ↔ x ∈ N.carrier ∧ (N.coordinate_inverse x).2 = s := by
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨N.coordinate_map_mem ⟨mem_univ _, hs0⟩,
          congrArg Prod.snd (N.coordinate_inverse_map _ hs0)⟩
      · rintro ⟨hx, hxheight⟩
        refine ⟨(N.coordinate_inverse x).1, ?_⟩
        rw [← hxheight]
        exact N.coordinate_map_inverse hx
    have hjdom {z : RoundCylinderSpace} (hz : z ∈ N'.cylinderDomain) : z ∈ e'.source :=
      he'source.symm ▸ hz
    have hjmem {z : RoundCylinderSpace} (hz : z ∈ N'.cylinderDomain) : e' z ∈ N'.carrier :=
      he'target ▸ e'.map_source (hjdom hz)
    have hjinv {x : M} (hx : x ∈ N'.carrier) : e'.symm x ∈ N'.cylinderDomain :=
      he'source ▸ e'.map_target (he'target.symm ▸ hx)
    have hequal {x : M} (hx : x ∈ N'.carrier) :
        x ∈ S ↔ (e'.symm x).2 = f (e'.symm x).1 := by
      change x ∈ range (fun p : UnitTwoSphere => N.coordinate_map (p, s)) ↔ _
      rw [hgs.2.2]
      constructor
      · rintro ⟨p, rfl⟩
        change (e'.symm (e' (p, f p))).2 = f (e'.symm (e' (p, f p))).1
        rw [e'.left_inv (hjdom (z := (p, f p)) ⟨mem_univ _, hfdom p⟩)]
      · intro hxheight
        refine ⟨(e'.symm x).1, ?_⟩
        change e' ((e'.symm x).1, f (e'.symm x).1) = x
        rw [← hxheight]
        exact e'.right_inv (he'target.symm ▸ hx)
    let Dminus : Set RoundCylinderSpace := {z | -N'.epsilon⁻¹ < z.2 ∧ z.2 < f z.1}
    let Dplus : Set RoundCylinderSpace := {z | f z.1 < z.2 ∧ z.2 < N'.epsilon⁻¹}
    let Wminus : Set M := e' '' Dminus
    let Wplus : Set M := e' '' Dplus
    have hminusD : Dminus ⊆ N'.cylinderDomain := by
      intro z hz
      exact ⟨mem_univ _, hz.1, hz.2.trans (hfdom z.1).2⟩
    have hplusD : Dplus ⊆ N'.cylinderDomain := by
      intro z hz
      exact ⟨mem_univ _, (hfdom z.1).1.trans hz.1, hz.2⟩
    have hminus : IsConnected Wminus :=
      (isConnected_between_continuous_graphs continuous_const hf (fun p => (hfdom p).1)).image
        e' (e'.continuousOn.mono (fun _ hz => hjdom (hminusD hz)))
    have hplus : IsConnected Wplus :=
      (isConnected_between_continuous_graphs hf continuous_const (fun p => (hfdom p).2)).image
        e' (e'.continuousOn.mono (fun _ hz => hjdom (hplusD hz)))
    have hminusV : Wminus ⊆ N'.carrier := by
      rintro x ⟨z, hz, rfl⟩
      exact hjmem (hminusD hz)
    have hplusV : Wplus ⊆ N'.carrier := by
      rintro x ⟨z, hz, rfl⟩
      exact hjmem (hplusD hz)
    have hmemMinus {x : M} (hx : x ∈ N'.carrier) :
        x ∈ Wminus ↔ (e'.symm x).2 < f (e'.symm x).1 := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [e'.left_inv (hjdom (hminusD hz))] using hz.2
      · intro hxheight
        exact ⟨e'.symm x, ⟨(hjinv hx).2.1, hxheight⟩,
          e'.right_inv (he'target.symm ▸ hx)⟩
    have hmemPlus {x : M} (hx : x ∈ N'.carrier) :
        x ∈ Wplus ↔ f (e'.symm x).1 < (e'.symm x).2 := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [e'.left_inv (hjdom (hplusD hz))] using hz.1
      · intro hxheight
        exact ⟨e'.symm x, ⟨hxheight, (hjinv hx).2.2⟩,
          e'.right_inv (he'target.symm ▸ hx)⟩
    let E : Set M := N.region (-N.epsilon⁻¹) s ∩ N'.carrier
    let K : Set M := N.coordinate_map '' (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) s)
    have hEopen : IsOpen E := (N.isOpen_region _ _).inter N'.carrier_open
    have hEK : E ⊆ K := by
      intro x hx
      have hxlo := (hoverlap ⟨hx.1.1, hx.2⟩).1.2.1
      exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hxlo.le, hx.1.2.2.le⟩,
        N.coordinate_map_inverse hx.1.1⟩
    have hKcompact : IsCompact K := N.isCompact_coordinate_slab (by linarith) hsret.2
    have hclosure : closure E ⊆ K := closure_minimal hEK hKcompact.isClosed
    have hKmem {x : M} (hx : x ∈ K) :
        x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ≤ s := by
      rcases hx with ⟨z, hz, rfl⟩
      have hzdom : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
        ⟨by linarith [hz.2.1], hz.2.2.trans_lt hsret.2⟩
      exact ⟨N.coordinate_map_mem ⟨mem_univ _, hzdom⟩,
        by simpa only [N.coordinate_inverse_map z hzdom] using hz.2.2⟩
    have hclosedBelow {x : M} (hx : x ∈ closure E) (hxV : x ∈ N'.carrier)
        (hxS : x ∉ S) : x ∈ E := by
      have hxK := hKmem (hclosure hx)
      have hxne : (N.coordinate_inverse x).2 ≠ s :=
        fun heq => hxS (hmemS.mpr ⟨hxK.1, heq⟩)
      exact ⟨⟨hxK.1, (N.coordinate_inverse_mem x hxK.1).2.1,
        lt_of_le_of_ne hxK.2 hxne⟩, hxV⟩
    have hclosureMinus : closure E ∩ Wminus ⊆ E := by
      intro x hx
      have hxV := hminusV hx.2
      apply hclosedBelow hx.1 hxV
      intro hxS
      exact ((hmemMinus hxV).mp hx.2).ne ((hequal hxV).mp hxS)
    have hclosurePlus : closure E ∩ Wplus ⊆ E := by
      intro x hx
      have hxV := hplusV hx.2
      apply hclosedBelow hx.1 hxV
      intro hxS
      exact ((hmemPlus hxV).mp hx.2).ne ((hequal hxV).mp hxS).symm
    let p₀ : UnitTwoSphere := (N.coordinate_inverse N.center).1
    let y : M := e' (p₀, 3 * N'.epsilon⁻¹ / 4)
    have hyD : (p₀, 3 * N'.epsilon⁻¹ / 4) ∈ Dplus := by
      constructor <;> linarith [(hfbound p₀).2]
    have hyplus : y ∈ Wplus := ⟨_, hyD, rfl⟩
    have hynot : y ∉ E := by
      intro hyE
      have hybound := (hoverlap ⟨hyE.1.1, hyE.2⟩).2.2.2
      rw [he'height _ (hplusD hyD)] at hybound
      linarith
    have hplusAvoid : Disjoint Wplus E := by
      apply Set.disjoint_left.mpr
      intro x hxplus hxE
      have hsub := hplus.isPreconnected.subset_of_closure_inter_subset hEopen
        ⟨x, hxplus, hxE⟩ hclosurePlus
      exact hynot (hsub hyplus)
    let r : ℝ := (N.epsilon⁻¹ / 2 + s) / 2
    let x₀ : M := N.coordinate_map (p₀, r)
    have hr : r ∈ Ioo (N.epsilon⁻¹ / 2) s := by
      dsimp only [r]
      constructor <;> linarith [hsret.1]
    have hrdom : r ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨by linarith [hr.1], hr.2.trans hsret.2⟩
    have hx₀old : x₀ ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hrdom⟩, ?_⟩
      simpa only [x₀, N.coordinate_inverse_map (p₀, r) hrdom, mem_Ioo] using
        (show r ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ from ⟨hr.1, hrdom.2⟩)
    have hx₀V : x₀ ∈ N'.carrier := hquarter hx₀old
    have hx₀E : x₀ ∈ E := by
      refine ⟨⟨hx₀old.1, ?_⟩, hx₀V⟩
      simpa only [x₀, N.coordinate_inverse_map (p₀, r) hrdom, mem_Ioo] using
        (show r ∈ Ioo (-N.epsilon⁻¹) s from ⟨hrdom.1, hr.2⟩)
    have hx₀notS : x₀ ∉ S := by
      intro hxS
      exact (hx₀E.1.2.2).ne (hmemS.mp hxS).2
    have hx₀minus : x₀ ∈ Wminus := by
      have hne : (e'.symm x₀).2 ≠ f (e'.symm x₀).1 :=
        fun heq => hx₀notS ((hequal hx₀V).mpr heq)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (hmemMinus hx₀V).mpr hlt
      · exact False.elim (Set.disjoint_left.mp hplusAvoid ((hmemPlus hx₀V).mpr hgt) hx₀E)
    have hminusE : Wminus ⊆ E :=
      hminus.isPreconnected.subset_of_closure_inter_subset hEopen
        ⟨x₀, hx₀minus, hx₀E⟩ hclosureMinus
    have hxtV : e (q, t) ∈ N'.carrier := henew ht
    have hxtnotS : e (q, t) ∉ S := by
      intro hxS
      have hxheight := (hmemS.mp hxS).2
      rw [heheight _ (hdom ht)] at hxheight
      exact hst.ne hxheight.symm
    have hxtnotMinus : e (q, t) ∉ Wminus := by
      intro hxminus
      have hxheight := (hminusE hxminus).1.2.2
      rw [heheight _ (hdom ht)] at hxheight
      exact (not_lt_of_gt hst) hxheight
    have hlt : f (e'.symm (e (q, t))).1 < (e'.symm (e (q, t))).2 := by
      have hne : (e'.symm (e (q, t))).2 ≠ f (e'.symm (e (q, t))).1 :=
        fun heq => hxtnotS ((hequal hxtV).mpr heq)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact False.elim (hxtnotMinus ((hmemMinus hxtV).mpr hlt))
      · exact hgt
    simpa only [f, hfirst (q, t) ht, A.symm_apply_apply] using hlt
  have hderiv : ∀ q : UnitTwoSphere, ∀ s ∈ Ioo a b,
      0 < deriv (fun r : ℝ => h (q, r)) s := by
    intro q s hs
    have hsclosed : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
    have hha : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun r : ℝ => h (q, r)) s :=
      (hhU.contMDiffAt ((e.trans e'.symm).open_source.mem_nhds
        (hclosedU hsclosed))).comp s
        (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    have hhd : DifferentiableAt ℝ (fun r : ℝ => h (q, r)) s :=
      (contMDiffAt_iff_contDiffAt.mp hha).differentiableAt (by norm_num)
    let V := (e'.trans N.coordinatePartialHomeomorph.symm).source
    let k : ℝ → ℝ := fun v => (N.coordinate_inverse (e' (A q, v))).2
    have hVdom {z : RoundCylinderSpace} (hz : z ∈ V) :
        z ∈ N'.cylinderDomain ∧ e' z ∈ N.carrier :=
      ⟨he'source ▸ hz.1, hz.2⟩
    have hkV : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z => (N.coordinate_inverse (e' z)).2) V :=
      contMDiff_snd.comp_contMDiffOn (N.coordinate_inverse_smooth.comp
        (he'.mono (fun _ hz => (hVdom hz).1)) (fun _ hz => (hVdom hz).2))
    have hv : (A q, h (q, s)) ∈ V := by
      change (A q, h (q, s)) ∈ e'.source ∧ e' (A q, h (q, s)) ∈ N.carrier
      refine ⟨he'source.symm ▸ hpairDom (q, s) hsclosed, ?_⟩
      rw [hforward (q, s) hsclosed]
      exact heold hsclosed
    have hka : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ k (h (q, s)) :=
      (hkV.contMDiffAt ((e'.trans N.coordinatePartialHomeomorph.symm).open_source.mem_nhds hv)).comp
        (h (q, s)) (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    have hkd : DifferentiableAt ℝ k (h (q, s)) :=
      (contMDiffAt_iff_contDiffAt.mp hka).differentiableAt (by norm_num)
    have hki : (fun r : ℝ => k (h (q, r))) =ᶠ[nhds s] id := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
      have hrc : r ∈ Icc a b := ⟨hr.1.le, hr.2.le⟩
      change (N.coordinate_inverse (e' (A q, h (q, r)))).2 = r
      rw [hforward (q, r) hrc]
      exact heheight (q, r) (hdom hrc)
    have hprod : deriv k (h (q, s)) * deriv (fun r : ℝ => h (q, r)) s = 1 := by
      rw [← deriv_comp s hkd hhd]
      exact hki.deriv_eq.trans (by simp)
    have hn : 0 ≤ deriv (fun r : ℝ => h (q, r)) s := by
      have hn := (hmono q).monotoneOn.derivWithin_nonneg (x := s)
      rwa [derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)] at hn
    have hne : deriv (fun r : ℝ => h (q, r)) s ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hprod
      exact zero_ne_one hprod
    exact lt_of_le_of_ne hn hne.symm
  obtain ⟨sigma, hsig, hsigmono, _, _, hsrc, htgt, htgtSub, hsmooth, hismooth,
      hforw, hback⟩ := e.exists_fiberwise_transition_band e' A.toHomeomorph hab
    (fun _ hz => hesource.symm ▸ hdom hz.2)
    (fun _ hz => he'target.symm ▸ henew hz.2) hfirst
    (hesource.symm ▸ he) (hetarget.symm ▸ hei)
    (he'source.symm ▸ he') (he'target.symm ▸ he'i)
  have hsigma : sigma = 1 := by
    rcases hsig with hs | hs
    · exact hs
    · let q₀ := (N.coordinate_inverse N.center).1
      have hp := hmono q₀ ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
      have hn := hsigmono q₀ ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
      simp only [hs, neg_one_mul] at hn
      exact False.elim (not_lt_of_gt hp (neg_lt_neg_iff.mp hn))
  subst sigma
  refine ⟨hgraph, hmono, hh, hderiv, hsrc, ?_, ?_, hsmooth, hismooth, hforw, hback⟩
  · simpa only [one_mul, Diffeomorph.coe_toHomeomorph_symm] using htgt
  · exact fun _ hz => he'source ▸ htgtSub hz

end PoincareConjecture.EpsilonNeck
