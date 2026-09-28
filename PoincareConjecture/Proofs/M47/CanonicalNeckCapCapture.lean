import PoincareConjecture.Proofs.M47.CanonicalNeckClosedDistance










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47


theorem neck_scale_le_cap_height_of_scalar {c D a h R : ℝ}
    (hc : 0 < c) (hD : 0 < D) (ha : 0 < a) (hh : 0 < h)
    (hfloor : c / (2 * h ^ 2) ≤ R) (hceiling : R ≤ D * (a⁻¹ ^ 2)) :
    a ≤ (1 + 2 * D / c) * h := by
  have hbound := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
    (sq_pos_of_pos hh))).mp (hfloor.trans hceiling)
  have hcross : c * a ^ 2 ≤ 2 * D * h ^ 2 := by
    calc
      _ ≤ (D * (a⁻¹ ^ 2) * (2 * h ^ 2)) * a ^ 2 :=
        mul_le_mul_of_nonneg_right hbound (sq_nonneg a)
      _ = _ := by field_simp [ha.ne']
  have hsquare : a ^ 2 ≤ (2 * D / c) * h ^ 2 := by
    apply (mul_le_mul_iff_left₀ hc).mp
    calc
      a ^ 2 * c = c * a ^ 2 := mul_comm _ _
      _ ≤ 2 * D * h ^ 2 := hcross
      _ = ((2 * D / c) * h ^ 2) * c := by field_simp
  have hratio : 0 < 2 * D / c := div_pos (mul_pos (by norm_num) hD) hc
  have hratioSq : 2 * D / c ≤ (1 + 2 * D / c) ^ 2 := by
    nlinarith [sq_nonneg (2 * D / c)]
  have hfinal : a ^ 2 ≤ ((1 + 2 * D / c) * h) ^ 2 := by
    rw [mul_pow]
    exact hsquare.trans (mul_le_mul_of_nonneg_right hratioSq (sq_nonneg h))
  nlinarith [mul_pos (show 0 < 1 + 2 * D / c by linarith) hh]



theorem exists_strongNeck_bottom_capture_radius (P : M47Predecessors.{u})
    (g0 : StandardInitialMetric) {epsilon c : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ 1 / 200) (hc : 0 < c) :
    ∃ A : ℝ, g0.cylindrical_end.radius + 5 < A ∧
      ∀ {F : SurgeryFlowData.{u}}, F.standard_initial = g0 →
      ∀ {T : ℝ} (N : SurgeryStrongNeck F T epsilon),
      ∀ (U : TopologicalSpace.Opens (F.slice T).carrier),
        (U : Set (F.slice T).carrier) = N.neck.carrier →
      ∀ E : SurgeryFlowCylinder F (F.slice T) T 1
          (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U,
        (∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) →
        (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
          (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
          ∀ x ∈ U,
            HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x)) →
        let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
        let ha : a ∈ Icc a 0 :=
          ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
        let t := T + a / 1
        ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
        ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
          E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
          c / (2 * (F.parameters.h t) ^ 2) ≤
            (F.connection t).scalarCurvature (E.forward a ha contact.val) →
          ∀ y : U, E.forward a ha y.val ∈
            (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) := by
  obtain ⟨D, hD, hscalar⟩ := exists_strongNeck_closed_scalar_bound P
  let d := 4 * (2 * Real.pi + 2 * epsilon⁻¹)
  let L := 1 + 2 * D / c
  let Acap := g0.cylindrical_end.radius + 5
  let A := Acap + 2 * d * L + 1
  have hd : 0 < d := by dsimp only [d]; positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  have hAcap : 0 < Acap := by
    dsimp only [Acap]
    linarith [g0.cylindrical_end.radius_pos]
  have hA : Acap < A := by
    dsimp only [A]
    nlinarith [mul_pos hd hL]
  refine ⟨A, hA, ?_⟩
  intro F hstandard T N U hU E hbased hagree
  dsimp only
  intro hT hn i contact hcontact hfloor y
  let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
  have ha : a ∈ Icc a 0 :=
    ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
  let t := T + a / 1
  let h := F.parameters.h t
  have hh : 0 < h :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hscalePos : 0 < N.neck.scale := N.neck.scale_pos
  have hR := hscalar N hsmall U hU E hbased hagree a ha contact
  have hratio : N.neck.scale ≤ L * h :=
    neck_scale_le_cap_height_of_scalar hc hD N.neck.scale_pos hh hfloor
      ((le_abs_self _).trans hR)
  have hdcontact := strongNeck_closed_center_distance P N hsmall U hU E hbased hagree
    a ha contact
  have hdy := strongNeck_closed_center_distance P N hsmall U hU E hbased hagree a ha y
  let g := F.metric t
  let center := E.forward a ha N.neck.center
  let z := E.forward a ha contact.val
  let w := E.forward a ha y.val
  let tip := ((F.event t hT).caps i).tip
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice t).carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsymm : g.edist z center = g.edist center z := Manifold.riemannianEDist_comm
  have hcontacty : g.edist z w ≤ ENNReal.ofReal (2 * d * N.neck.scale) := by
    calc
      _ ≤ g.edist z center + g.edist center w := Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal (d * N.neck.scale) + ENNReal.ofReal (d * N.neck.scale) := by
        rw [hsymm]
        exact add_le_add hdcontact hdy
      _ = _ := by
        rw [← ENNReal.ofReal_add (mul_pos hd N.neck.scale_pos).le
          (mul_pos hd N.neck.scale_pos).le]
        congr 1
        ring
  have houter : g.edist tip z ≤ ENNReal.ofReal (Acap * h) := by
    have ho := ((F.event t hT).caps i).outer_ball hcontact
    change (F.metric t).edist ((F.event t hT).caps i).tip z ≤
      ENNReal.ofReal (F.parameters.h t * (F.standard_initial.cylindrical_end.radius + 5))
      at ho
    have hAcapEq : F.standard_initial.cylindrical_end.radius + 5 = Acap :=
      congrArg (fun g0 : StandardInitialMetric => g0.cylindrical_end.radius + 5) hstandard
    rw [hAcapEq] at ho
    simpa only [g, tip, h, mul_comm] using ho
  have hsum : 0 ≤ Acap * h + 2 * d * N.neck.scale := by positivity
  have hstrict : Acap * h + 2 * d * N.neck.scale < A * h := by
    have hscaled := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2 * d)
    dsimp only [A]
    nlinarith only [hscaled, hh]
  change g.edist tip w < ENNReal.ofReal (A * h)
  calc
    _ ≤ g.edist tip z + g.edist z w := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal (Acap * h) + ENNReal.ofReal (2 * d * N.neck.scale) :=
      add_le_add houter hcontacty
    _ = ENNReal.ofReal (Acap * h + 2 * d * N.neck.scale) :=
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (hsum.trans_lt hstrict)).mpr hstrict

end PoincareConjecture.Proofs.M47
