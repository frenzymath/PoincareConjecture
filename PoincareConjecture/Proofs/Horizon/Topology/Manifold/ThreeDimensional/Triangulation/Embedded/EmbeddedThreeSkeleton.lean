import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Ambient.AmbientSimplicialGrid
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Ambient.AmbientSlabAvoidance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Ambient.AmbientGridPerturbation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Embedded.EmbeddedThreeTangent

set_option autoImplicit false

noncomputable section

open scoped BigOperators Manifold ContDiff Topology

universe u

namespace Poincare.Topology

set_option maxHeartbeats 6000000 in

theorem exists_embedded_three_avoiding_ambient_grid
    {N : Nat} (hN : 3 < N) {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
    (e : C(M, EuclideanSpace Real (Fin N)))
    (hs : ContMDiff (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) ∞ e)
    (he : _root_.Topology.IsClosedEmbedding e)
    (hi : ∀ p : M, Function.Injective
      (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e p))
    (hmax : Real) (hhmax : 0 < hmax) :
    ∃ h : Real, 0 < h ∧ h < hmax ∧ ∃ B : Nat, 0 < B ∧
    ∃ w : (Fin N → Int) → EuclideanSpace Real (Fin N),
    ∃ H : EuclideanSpace Real (Fin N) ≃ₜ EuclideanSpace Real (Fin N),
    ∃ K : Geometry.SimplicialComplex Real (EuclideanSpace Real (Fin N)),
      Set.Finite {z | w z ≠ ambientGridPoint h z} ∧
      (∀ z, dist (w z) (ambientGridPoint h z) ≤ ambientGridMoveRatio N * h) ∧
      (∀ z, H (ambientGridPoint h z) = w z) ∧
      (∀ x, dist (H x) x ≤ ambientGridMoveRatio N * h) ∧
      LipschitzWith (1 / 4 : NNReal) (fun x => H x - x) ∧
      (∀ z pi, ∃ A : EuclideanSpace Real (Fin N) →ᵃ[Real]
          EuclideanSpace Real (Fin N),
        ∀ x ∈ convexHull Real (ambientGridSimplex (N := N) h z pi :
          Set (EuclideanSpace Real (Fin N))), H x = A x) ∧
      K.faces = {s | ∃ t ∈ ambientGridFaces h B, s = t.image H} ∧
      Set.Finite K.faces ∧
      (∀ x, Metric.infDist x (Set.range e) ≤ 10 * (N + 1 : Real) * h →
        x ∈ K.space) ∧
      (∀ s ∈ K.faces, s.card ≤ N + 1 ∧
        Metric.diam (convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) ≤
          2 * (N + 1 : Real) * h ∧
        (2 ≤ s.card → ∀ v ∈ s,
          h / 4 ≤ Metric.infDist v
            (affineSpan Real ((s.erase v : Finset (EuclideanSpace Real (Fin N))) :
              Set (EuclideanSpace Real (Fin N))) : Set (EuclideanSpace Real (Fin N))))) ∧
      (∀ v ∈ K.vertices,
        Set.ncard {s | s ∈ K.faces ∧ v ∈ s} ≤ ambientGridStarBound N) ∧
      (∀ s ∈ K.faces, s.card + 3 ≤ N →
        ∀ x ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N))),
          ambientGridGap N (N - 4) * h < Metric.infDist x (Set.range e)) := by
  classical
  let E := EuclideanSpace Real (Fin N)
  let S : Set E := Set.range e
  let L : Real := N + 1
  let rho := ambientGridMoveRatio N
  let nu := ambientGridSlabRatio N
  let A := rho * nu
  let b := ambientGridGap N
  have hL : 1 ≤ L := by
    have hn : (0 : Real) ≤ N := Nat.cast_nonneg N
    dsimp [L]
    linarith
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hrho : 0 < rho := by dsimp [rho, ambientGridMoveRatio]; positivity
  have hrho' : rho ≤ 1 / 16 := by
    change 1 / (16 * L) ≤ 1 / 16
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have hnu : 0 < nu := by dsimp [nu, ambientGridSlabRatio]; positivity
  have hnu' : nu ≤ 1 / 4 := by
    change 1 / (4 * L ^ 2 * (ambientGridStarBound N + 1 : Real)) ≤ 1 / 4
    have hj : (1 : Real) ≤ ambientGridStarBound N + 1 := by
      have : (0 : Real) ≤ ambientGridStarBound N := by positivity
      linarith
    have hsq : 1 ≤ L ^ 2 := by nlinarith
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have hp := mul_le_mul hsq hj (by norm_num : (0 : Real) ≤ 1) (sq_nonneg L)
    nlinarith
  have hA : 0 < A := mul_pos hrho hnu
  have hA' : A ≤ 1 / 64 := by
    have hh := mul_le_mul hrho' hnu' hnu.le (by norm_num)
    norm_num at hh
    exact hh
  have hb (r : Nat) : b r = (A / 2) * (A / (8 * L)) ^ r := rfl
  have hbpos (r : Nat) : 0 < b r := by rw [hb]; positivity
  have hratio : A / (8 * L) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hbmono {r s : Nat} (hrs : r ≤ s) : b s ≤ b r := by
    rw [hb, hb]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by positivity) hratio hrs) (by positivity)
  have hbzero : b 0 = A / 2 := by rw [hb]; simp
  have hble (r : Nat) : b r ≤ A / 2 := by simpa [hbzero] using hbmono (Nat.zero_le r)
  have hbsucc (r : Nat) : b (r + 1) = b r * A / (8 * L) := by
    rw [hb, hb, pow_succ]
    ring
  let epsilon : NNReal := ⟨b (N - 4) / (1000 * L), by
    exact (div_pos (hbpos (N - 4)) (by positivity)).le⟩
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos (hbpos (N - 4)) (by positivity)
  obtain ⟨R, hR, hg⟩ := exists_uniform_embedded_three_graph e hs he hi epsilon hepsilon
  let h := min hmax (R / (13 * L)) / 2
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax' : h < hmax := by
    have hhmin := min_le_left hmax (R / (13 * L))
    dsimp [h]
    linarith
  let delta := L * h
  have hdelt : 0 < delta := mul_pos hLp hh
  have hsmall : 12 * delta < R := by
    have hhmin := min_le_right hmax (R / (13 * L))
    have hhh : h ≤ R / (13 * L) / 2 := by dsimp [h]; linarith
    have hmul := (le_div_iff₀ (by positivity : (0 : Real) < 13 * L)).mp
      (show 2 * h ≤ R / (13 * L) by linarith)
    dsimp [delta]
    nlinarith
  have hmove : rho * h < delta := by dsimp [delta]; nlinarith
  have hmove2 : delta + 2 * (rho * h) < 2 * delta := by dsimp [delta]; nlinarith
  have hblt (r : Nat) : b r * h < delta := by
    have hb' := hble r
    dsimp [delta]
    nlinarith
  let err := b (N - 4) * h / 100
  have herrpos : 0 < err := by
    dsimp [err]
    exact div_pos (mul_pos (hbpos (N - 4)) hh) (by norm_num)
  have heps : (epsilon : Real) * (7 * delta) ≤ err := by
    have heq : (epsilon : Real) * (7 * delta) = (7 / 1000 : Real) * (b (N - 4) * h) := by
      change (b (N - 4) / (1000 * L)) * (7 * (L * h)) = _
      field_simp [hLp.ne']
    rw [heq]
    dsimp [err]
    nlinarith [mul_pos (hbpos (N - 4)) hh]
  have hSne : S.Nonempty := Set.range_nonempty e
  have hSc : IsCompact S := isCompact_range e.continuous
  let P (p : M) : AffineSubspace Real E := AffineSubspace.mk' (e p) (embeddedThreeTangent e p)
  have hgraph (p : M) :
      (∀ q : E, dist q (e p) < 6 * delta →
        Metric.infDist q S ≤ Metric.infDist q (P p : Set E) + err) ∧
      (∀ y : M, dist (e y) (e p) < 7 * delta → ∀ x : E,
        Metric.infDist x (P p : Set E) ≤ dist x (e y) + err) := by
    obtain ⟨g, hsource, hgzero, hcoord, hglip, hcover⟩ := hg p
    let T := embeddedThreeTangent e p
    have hzero : (0 : T) ∈ g.source := by
      rw [hsource]
      simpa using (show (0 : Real) < 2 * R by positivity)
    have herror (v : T) (hv : v ∈ g.source) :
        ‖e (g v) - e p - (v : E)‖ ≤ (epsilon : Real) * ‖v‖ := by
      simpa [hgzero] using hglip.dist_le_mul v hv 0 hzero
    have hnorm (q : E) : ‖T.orthogonalProjectionOnto (q - e p)‖ ≤ dist q (e p) := by
      calc
        ‖T.orthogonalProjectionOnto (q - e p)‖ ≤ ‖q - e p‖ :=
          T.norm_orthogonalProjectionOnto_apply_le (q - e p)
        _ = dist q (e p) := (dist_eq_norm q (e p)).symm
    have hproj (q : E) : (EuclideanGeometry.orthogonalProjection (P p) q : E) =
        e p + (T.orthogonalProjectionOnto (q - e p) : E) := by
      simpa [P, T, AffineSubspace.direction_mk', vsub_eq_sub, vadd_eq_add, add_comm] using
        EuclideanGeometry.orthogonalProjection_apply_mem (P p)
          (p := q) (x := e p)
          (AffineSubspace.self_mem_mk' (e p) (embeddedThreeTangent e p))
    have herrdist (v : T) (hv : v ∈ g.source) :
        dist (e p + (v : E)) (e (g v)) ≤ (epsilon : Real) * ‖v‖ := by
      calc
        dist (e p + (v : E)) (e (g v)) = ‖e (g v) - e p - (v : E)‖ := by
          rw [dist_comm, dist_eq_norm]
          congr 1
          abel
        _ ≤ _ := herror v hv
    constructor
    · intro q hq
      let v := T.orthogonalProjectionOnto (q - e p)
      have hvnorm : ‖v‖ < 6 * delta := (hnorm q).trans_lt hq
      have hv : v ∈ g.source := by rw [hsource, Metric.mem_ball, dist_zero_right]; linarith
      have hd := herrdist v hv
      have hd' : dist (e p + (v : E)) (e (g v)) ≤ err :=
        hd.trans ((mul_le_mul_of_nonneg_left (by linarith : ‖v‖ ≤ 7 * delta)
          (NNReal.coe_nonneg epsilon)).trans heps)
      have hpdist : dist q (e p + (v : E)) = Metric.infDist q (P p : Set E) := by
        rw [← hproj q]
        exact EuclideanGeometry.dist_orthogonalProjection_eq_infDist (P p) q
      calc
        Metric.infDist q S ≤ dist q (e (g v)) := Metric.infDist_le_dist_of_mem ⟨g v, rfl⟩
        _ ≤ dist q (e p + (v : E)) + dist (e p + (v : E)) (e (g v)) := dist_triangle _ _ _
        _ ≤ Metric.infDist q (P p : Set E) + err := by rw [hpdist]; linarith
    · intro y hy x
      have hyt : y ∈ g.target := hcover y (by linarith)
      let v := g.symm y
      have hv : v ∈ g.source := g.map_target hyt
      have hgv : g v = y := g.right_inv hyt
      have hcv : T.orthogonalProjectionOnto (e y - e p) = v := by
        simpa only [hgv] using hcoord v hv
      have hvnorm : ‖v‖ < 7 * delta := by rw [← hcv]; exact (hnorm (e y)).trans_lt hy
      have hd : dist (e p + (v : E)) (e y) ≤ err := by
        rw [← hgv]
        exact (herrdist v hv).trans ((mul_le_mul_of_nonneg_left hvnorm.le
          (NNReal.coe_nonneg epsilon)).trans heps)
      have hmem : e p + (v : E) ∈ P p := by
        change e p + (v : E) - e p ∈ T
        simp
      calc
        Metric.infDist x (P p : Set E) ≤ dist x (e p + (v : E)) :=
          Metric.infDist_le_dist_of_mem hmem
        _ ≤ dist x (e y) + dist (e y) (e p + (v : E)) := dist_triangle _ _ _
        _ ≤ dist x (e y) + err := by rw [dist_comm (e y)]; linarith
  obtain ⟨R0, hR0, hSbound⟩ := hSc.isBounded.subset_closedBall_lt 0 (0 : E)
  let lattice : Set E := Set.range (ambientGridPoint (N := N) h)
  let active : Set E := {v | v ∈ lattice ∧ Metric.infDist v S < 3 * delta}
  have hcorner (z : Fin N → Int) :
      ambientGridPoint h z ∈ ambientGridSimplex h z (Equiv.refl (Fin N)) := by
    apply Finset.mem_image.mpr
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
    change ambientGridCorner h z (Equiv.refl (Fin N)) ⟨0, by omega⟩ = _
    simp [ambientGridCorner, ambientGridPoint]
  have hactivefinite : active.Finite := by
    let C := {q : (Fin N → Int) × Equiv.Perm (Fin N) |
      (convexHull Real (ambientGridSimplex h q.1 q.2 : Set E) ∩
        Metric.closedBall (0 : E) (R0 + 3 * delta)).Nonempty}
    have hC : C.Finite := ambient_grid_faces_locally_finite h hh 0 (R0 + 3 * delta)
    have hunion : (⋃ q ∈ C, (ambientGridSimplex h q.1 q.2 : Set E)).Finite :=
      hC.biUnion (fun q _ => (ambientGridSimplex h q.1 q.2).finite_toSet)
    apply hunion.subset
    rintro v ⟨⟨z, rfl⟩, hv⟩
    obtain ⟨q, hq, hd⟩ := (Metric.infDist_lt_iff hSne).mp hv
    have hqn : dist q 0 ≤ R0 := hSbound hq
    have hvn : ambientGridPoint h z ∈ Metric.closedBall (0 : E) (R0 + 3 * delta) := by
      rw [Metric.mem_closedBall]
      have ht := dist_triangle (ambientGridPoint h z) q 0
      linarith
    have hcell : (z, Equiv.refl (Fin N)) ∈ C :=
      ⟨ambientGridPoint h z, subset_convexHull Real _ (hcorner z), hvn⟩
    exact Set.mem_iUnion.mpr ⟨(z, Equiv.refl (Fin N)), Set.mem_iUnion.mpr ⟨hcell, hcorner z⟩⟩
  let V := hactivefinite.toFinset
  have hV (v : E) : v ∈ V ↔ v ∈ lattice ∧ Metric.infDist v S < 3 * delta := by
    simp only [V, Set.Finite.mem_toFinset, active, Set.mem_ofPred_eq]
  let Face (s : Finset E) : Prop := s.Nonempty ∧ ∃ z pi, s ⊆ ambientGridSimplex h z pi
  have hvertex {s : Finset E} (hsf : Face s) {v : E} (hv : v ∈ s) : v ∈ lattice := by
    obtain ⟨z, pi, hsub⟩ := hsf.2
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (hsub hv)
    exact ⟨fun i => z i + if (pi.symm i).val < k.val then 1 else 0, rfl⟩
  have hdist {s : Finset E} (hsf : Face s) {v w : E} (hv : v ∈ s) (hw : w ∈ s) :
      dist v w ≤ delta := by
    obtain ⟨z, pi, hsub⟩ := hsf.2
    exact (Metric.dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull Real).isBounded
      (subset_convexHull Real _ hv) (subset_convexHull Real _ hw)).trans
      (ambient_grid_simplex_geometry h hh z pi s hsf.1 hsub).2.2.1
  have hdiam (f : E → E) (hf : ∀ v ∈ lattice, dist (f v) v ≤ rho * h)
      {s : Finset E} (hsf : Face s) {x y : E}
      (hx : x ∈ convexHull Real (s.image f : Set E))
      (hy : y ∈ convexHull Real (s.image f : Set E)) : dist x y < 2 * delta := by
    obtain ⟨x', hx', y', hy', hxy⟩ := convexHull_exists_dist_ge2 hx hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
    have hv' := hf v (hvertex hsf hv)
    have hw' := hf w (hvertex hsf hw)
    have hd := hdist hsf hv hw
    have ht1 := dist_triangle (f v) v (f w)
    have ht2 := dist_triangle v w (f w)
    rw [dist_comm w (f w)] at ht2
    linarith
  have hfar (f : E → E) (hfix : ∀ v, v ∉ V → f v = v)
      (hf : ∀ v ∈ lattice, dist (f v) v ≤ rho * h)
      {s : Finset E} (hsf : Face s) {a : E} (ha : a ∈ s) (hain : a ∉ V)
      (x : E) (hx : x ∈ convexHull Real (s.image f : Set E)) (r : Nat) :
      b r * h < Metric.infDist x S := by
    have ha' : 3 * delta ≤ Metric.infDist a S := by
      by_contra hh'
      exact hain ((hV a).mpr ⟨hvertex hsf ha, lt_of_not_ge hh'⟩)
    have haim : a ∈ convexHull Real (s.image f : Set E) := by
      apply subset_convexHull Real _
      exact Finset.mem_image.mpr ⟨a, ha, hfix a hain⟩
    have hd := hdiam f hf hsf hx haim
    have hi' := Metric.infDist_le_infDist_add_dist (s := S) (x := a) (y := x)
    rw [dist_comm a x] at hi'
    have hb' := hblt r
    linarith
  have htransfer (p : M) (r : Nat) (hr : r ≤ N - 4) (x : E)
      (hx : dist x (e p) < 6 * delta)
      (hxp : (3 / 2 : Real) * b r * h ≤ Metric.infDist x (P p : Set E)) :
      b r * h < Metric.infDist x S := by
    obtain ⟨q, ⟨y, rfl⟩, hq⟩ := hSc.exists_infDist_eq_dist hSne x
    by_cases hnear : dist x (e y) < delta
    · have hyp : dist (e y) (e p) < 7 * delta := by
        have ht := dist_triangle (e y) x (e p)
        rw [dist_comm (e y) x] at ht
        linarith
      have hb' := (hgraph p).2 y hyp x
      have herr : err ≤ b r * h / 100 := by
        dsimp [err]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbmono hr) hh.le) (by norm_num)
      rw [hq]
      nlinarith [mul_pos (hbpos r) hh]
    · rw [hq]
      exact (hblt r).trans_le (le_of_not_gt hnear)

  have hind : ∀ U : Finset E, U ⊆ V → ∃ f : E → E,
      (∀ v, v ∉ U → f v = v) ∧
      (∀ v ∈ lattice, dist (f v) v ≤ rho * h) ∧
      (∀ s : Finset E, Face s → (∀ v ∈ s, v ∈ V → v ∈ U) → s.card + 3 ≤ N →
        ∀ x ∈ convexHull Real (s.image f : Set E), b (s.card - 1) * h < Metric.infDist x S) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨id, by simp, ?_, ?_⟩
      · intro v _
        exact (dist_self v).le.trans (mul_pos hrho hh).le
      · intro s hsf hcomp _ x hx
        obtain ⟨a, ha⟩ := hsf.1
        have hain : a ∉ V := fun hh' => Finset.notMem_empty a (hcomp a ha hh')
        exact hfar id (by simp)
          (by intro v _; exact (dist_self v).le.trans (mul_pos hrho hh).le)
          hsf ha hain x hx (s.card - 1)
    | @insert v U hvU ih =>
      intro hins
      have hU : U ⊆ V := fun a ha => hins (Finset.mem_insert_of_mem ha)
      have hvV : v ∈ V := hins (Finset.mem_insert_self v U)
      obtain ⟨f, hfix, hf, hclear⟩ := ih hU
      obtain ⟨q, ⟨p, rfl⟩, hvp⟩ := (Metric.infDist_lt_iff hSne).mp ((hV v).mp hvV).2
      let F : Set (Finset E) := {s | Face s ∧ v ∈ s ∧ s.card + 3 ≤ N ∧
        ∀ a ∈ s, a ≠ v → a ∈ U}
      let star : Set (Finset E) := {s | s.Nonempty ∧ v ∈ s ∧ ∃ z pi, s ⊆ ambientGridSimplex h z pi}
      have hstar := ambient_grid_star_count h hh v
      have hFsub : F ⊆ star := fun s hs' => ⟨hs'.1.1, hs'.2.1, hs'.1.2⟩
      have hFfin : F.Finite := hstar.1.subset hFsub
      let : Fintype F := hFfin.fintype
      let m := Fintype.card F
      let ix : Fin m ≃ F := (Fintype.equivFin F).symm
      have hm : m ≤ ambientGridStarBound N := by
        change Fintype.card F ≤ _
        rw [Set.fintypeCard_eq_ncard]
        exact (Set.ncard_le_ncard hFsub hstar.1).trans hstar.2
      let Q (s : Finset E) := (s.erase v).image f
      let Ps (s : Finset E) : AffineSubspace Real E := AffineSubspace.mk' (e p)
        (embeddedThreeTangent e p ⊔ Submodule.span Real (Q s |>.image (fun q => q - e p) : Set E))
      have hPP (s : Finset E) : P p ≤ Ps s :=
        (AffineSubspace.mk'_le_mk'_iff (e p)).mpr le_sup_left
      have hQP (s : Finset E) (q : E) (hq : q ∈ Q s) : q ∈ Ps s := by
        change q - e p ∈ embeddedThreeTangent e p ⊔ _
        apply Submodule.mem_sup_right
        exact Submodule.subset_span (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      have hdim (s : Finset E) (hs' : s ∈ F) : Module.finrank Real (Ps s).direction < N := by
        have hcard : (s.erase v).card = s.card - 1 := Finset.card_erase_of_mem hs'.2.1
        have hqcard : (Q s).card ≤ s.card - 1 := by
          exact (Finset.card_image_le).trans hcard.le
        have hspan : Module.finrank Real
            (Submodule.span Real ((Q s).image (fun q => q - e p) : Set E)) ≤ (Q s).card :=
          (finrank_span_finset_le_card (R := Real) _).trans Finset.card_image_le
        have hrank := Submodule.finrank_add_le_finrank_add_finrank
          (embeddedThreeTangent e p)
          (Submodule.span Real ((Q s).image (fun q => q - e p) : Set E))
        rw [embeddedThreeTangent_finrank e p (hi p)] at hrank
        have hsbound := hs'.2.2.1
        let D : Submodule Real E := embeddedThreeTangent e p ⊔ Submodule.span Real
          ((Q s).image (fun q => q - e p) : Set E)
        have hdir_le : Module.finrank Real D ≤ 3 + (Q s).card := by
          dsimp [D]
          exact hrank.trans (by
            simpa [add_comm] using (Nat.add_le_add_left hspan 3))
        have hdir : Module.finrank Real D < N := by
          omega
        change Module.finrank Real (AffineSubspace.mk' (e p) D).direction < N
        rw [AffineSubspace.direction_mk']
        exact hdir
      obtain ⟨a, ha, havoid⟩ := exists_ball_point_avoiding_affine_planes (by omega : 0 < N)
        v (rho * h) (mul_pos hrho hh) (fun i : Fin m => Ps (ix i).val)
        (fun _ => AffineSubspace.mk'_nonempty _ _) (fun i => hdim _ (ix i).property)
      let wv := ambientAvoidanceGridPoint v (rho * h) a
      have hwv : dist wv v < rho * h := ha
      have hsep (s : Finset E) (hs' : s ∈ F) : A * h < Metric.infDist wv (Ps s : Set E) := by
        have hden : A * h ≤ rho * h / (4 * L ^ 2 * (m + 1 : Real)) := by
          have hm' : (m : Real) ≤ ambientGridStarBound N := by exact_mod_cast hm
          calc
            A * h = rho * h / (4 * L ^ 2 * (ambientGridStarBound N + 1 : Real)) := by
              dsimp [A, nu, ambientGridSlabRatio, L]
              ring
            _ ≤ _ := div_le_div_of_nonneg_left (mul_pos hrho hh).le (by positivity)
              (by gcongr)
        have hi' := havoid (ix.symm ⟨s, hs'⟩)
        simpa only [Equiv.apply_symm_apply] using hden.trans_lt hi'
      let f' : E → E := Function.update f v wv
      have hfv : f' v = wv := by simp [f']
      have hfix' (a : E) (ha : a ∉ insert v U) : f' a = a := by
        have hav : a ≠ v := by intro h'; apply ha; simp [h']
        have haU : a ∉ U := fun h' => ha (Finset.mem_insert_of_mem h')
        simpa [f', hav] using hfix a haU
      have hf' : ∀ a ∈ lattice, dist (f' a) a ≤ rho * h := by
        intro a ha
        by_cases hav : a = v
        · subst a
          simpa only [hfv] using hwv.le
        · simpa [f', hav] using hf a ha
      refine ⟨f', hfix', hf', ?_⟩
      intro s hsf hcomp hsc x hx
      by_cases hall : ∀ a ∈ s, a ∈ V
      · by_cases hsv : v ∈ s
        · have hsF : s ∈ F := by
            refine ⟨hsf, hsv, hsc, ?_⟩
            intro a ha hav
            exact (Finset.mem_insert.mp (hcomp a ha (hall a ha))).resolve_left hav
          have hQeq : (s.erase v).image f' = Q s := by
            apply Finset.image_congr
            intro a ha
            exact Function.update_of_ne (Finset.mem_erase.mp ha).1 wv f
          have himage : s.image f' = insert wv (Q s) := by
            conv_lhs => rw [← Finset.insert_erase hsv]
            rw [Finset.image_insert, hQeq, hfv]
          have hQsub : (Q s : Set E) ⊆ (s.image f' : Set E) := by
            rw [himage]
            exact Finset.subset_insert _ _
          have hwmem : wv ∈ convexHull Real (s.image f' : Set E) := by
            apply subset_convexHull Real _
            exact Finset.mem_image.mpr ⟨v, hsv, hfv⟩
          have hnear (y : E) (hy : y ∈ convexHull Real (s.image f' : Set E)) :
              dist y (e p) < 6 * delta := by
            have hd := hdiam f' hf' hsf hy hwmem
            have ht1 := dist_triangle y wv (e p)
            have ht2 := dist_triangle wv v (e p)
            linarith
          apply htransfer p (s.card - 1) (by omega) x (hnear x hx)
          by_cases heq : (s.erase v).Nonempty
          · have herase : (s.erase v).card = s.card - 1 := Finset.card_erase_of_mem hsv
            have hr : 0 < s.card - 1 := by have := Finset.card_pos.mpr heq; omega
            have heraseface : Face (s.erase v) := by
              obtain ⟨z, pi, hsub⟩ := hsf.2
              exact ⟨heq, z, pi, (Finset.erase_subset v s).trans hsub⟩
            have hbprev : b (N - 4) ≤ b ((s.card - 1) - 1) := hbmono (by omega)
            have hsepQ : ∀ q ∈ convexHull Real (Q s : Set E),
                (2 / 3 : Real) * b ((s.card - 1) - 1) * h ≤ Metric.infDist q (P p : Set E) := by
              intro q hq
              have hqclear := hclear (s.erase v) heraseface
                (fun a ha _ => hsF.2.2.2 a (Finset.mem_erase.mp ha).2 (Finset.mem_erase.mp ha).1)
                (by omega) q hq
              rw [herase] at hqclear
              have hqn := hnear q (convexHull_mono hQsub hq)
              have hforward := (hgraph p).1 q hqn
              have herr : err ≤ b ((s.card - 1) - 1) * h / 100 := by
                dsimp [err]
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hbprev hh.le) (by norm_num)
              nlinarith [mul_pos (hbpos ((s.card - 1) - 1)) hh]
            have hj := affine_join_distance_lower_bound (P p) (Ps s)
              (AffineSubspace.mk'_nonempty _ _) (hPP s) (Q s) (heq.image f) (hQP s)
              wv ((2 / 3 : Real) * b ((s.card - 1) - 1) * h) (A * h) (2 * delta)
              (mul_pos (mul_pos (by norm_num) (hbpos _)) hh)
              (mul_pos hA hh) (by nlinarith) hsepQ (hsep s hsF).le
              (fun q hq => (hdiam f' hf' hsf hwmem (convexHull_mono hQsub hq)).le)
              x (by simpa only [himage] using hx)
            have hrec : b (s.card - 1) * (8 * L) = b ((s.card - 1) - 1) * A := by
              have hh' := hbsucc ((s.card - 1) - 1)
              rw [Nat.sub_add_cancel hr] at hh'
              exact (eq_div_iff (by positivity)).mp hh'
            have hAh : A * h ≤ delta := by dsimp [delta]; nlinarith
            have hprod : 0 ≤ b (s.card - 1) * L * h ^ 2 := by
              exact mul_nonneg (mul_nonneg (hbpos _).le hLp.le) (sq_nonneg h)
            have hjoin : (3 / 2 : Real) * b (s.card - 1) * h ≤
                ((2 / 3 : Real) * b ((s.card - 1) - 1) * h) * (A * h) /
                  (2 * delta + A * h) := by
              apply (le_div_iff₀ (by positivity)).mpr
              calc
                    (3 / 2 : Real) * b (s.card - 1) * h * (2 * delta + A * h) ≤
                    (3 / 2 : Real) * b (s.card - 1) * h * (3 * delta) := by
                      apply mul_le_mul_of_nonneg_left
                      · linarith
                      · exact mul_nonneg (mul_nonneg (by norm_num) (hbpos _).le) hh.le
                _ = (9 / 2 : Real) * (b (s.card - 1) * L * h ^ 2) := by dsimp [delta]; ring
                _ ≤ (16 / 3 : Real) * (b (s.card - 1) * L * h ^ 2) := by nlinarith
                _ = (2 / 3 : Real) * (b (s.card - 1) * (8 * L)) * h ^ 2 := by ring
                _ = ((2 / 3 : Real) * b ((s.card - 1) - 1) * h) * (A * h) := by rw [hrec]; ring
            exact hjoin.trans hj
          · have herase : s.erase v = ∅ := Finset.not_nonempty_iff_eq_empty.mp heq
            have hsone : s = {v} := by simpa [herase] using
              (Finset.insert_erase hsv).symm
            have hQ : Q s = ∅ := by simp [Q, herase]
            have hxw : x = wv := by simpa [himage, hQ] using hx
            have hps : Ps s = P p := by simp [Ps, hQ, P]
            have hse := hsep s hsF
            rw [hps] at hse
            rw [hxw, hsone]
            simp only [Finset.card_singleton, Nat.sub_self, hbzero]
            nlinarith [mul_pos hA hh]
        · have hcomp' : ∀ a ∈ s, a ∈ V → a ∈ U := by
            intro a ha haV
            have hav : a ≠ v := by intro hh'; subst a; exact hsv ha
            exact (Finset.mem_insert.mp (hcomp a ha haV)).resolve_left hav
          have himage : s.image f' = s.image f := by
            apply Finset.image_congr
            intro a ha
            have hav : a ≠ v := fun hav => hsv (hav ▸ ha)
            exact Function.update_of_ne hav wv f
          exact hclear s hsf hcomp' hsc x (by simpa only [himage] using hx)
      · push Not at hall
        obtain ⟨a, ha, hain⟩ := hall
        exact hfar f' (fun a ha => hfix' a (fun ha' => ha (hins ha'))) hf' hsf ha hain x hx
          (s.card - 1)
  obtain ⟨f, hfix, hf, hclear⟩ := hind V le_rfl
  let w (z : Fin N → Int) := f (ambientGridPoint h z)
  have hgp : Function.Injective (ambientGridPoint (N := N) h) := by
    intro z z' heq
    funext i
    have heq' := congrArg (fun x : E => x i) heq
    change h * (z i : Real) = h * (z' i : Real) at heq'
    exact_mod_cast (mul_left_cancel₀ hh.ne' heq')
  have hsupport : Set.Finite {z | w z ≠ ambientGridPoint h z} := by
    apply (Set.Finite.preimage hgp.injOn V.finite_toSet).subset
    intro z hz
    by_contra hnot
    exact hz (hfix (ambientGridPoint h z) hnot)
  have hw : ∀ z, dist (w z) (ambientGridPoint h z) ≤ ambientGridMoveRatio N * h :=
    fun z => hf _ ⟨z, rfl⟩
  obtain ⟨H, hHw, hHd, hHl, hHa⟩ := exists_ambient_grid_perturbation h hh w hw
  obtain ⟨B, hB⟩ := exists_nat_gt (max (1 : Real) ((R0 + 11 * delta) / h))
  have hBp : 0 < B := by
    have hb' : (1 : Real) < B := (le_max_left _ _).trans_lt hB
    exact_mod_cast (lt_trans zero_lt_one hb')
  have hBbig : R0 + 11 * delta < (B : Real) * h :=
    (div_lt_iff₀ hh).mp ((le_max_right _ _).trans_lt hB)
  obtain ⟨K, hKf, hKfin, hKs, hKgeom, hKstar⟩ :=
    exists_perturbed_ambient_grid_complex h hh B hBp H hHl hHa
  refine ⟨h, hh, hhmax', B, hBp, w, H, K, hsupport, hw, hHw, hHd, hHl, hHa,
    hKf, hKfin, ?_, hKgeom, hKstar, ?_⟩
  · intro x hx
    change Metric.infDist x S ≤ 10 * L * h at hx
    obtain ⟨q, hq, hqx⟩ := hSc.exists_infDist_eq_dist hSne x
    have hqn : dist q 0 ≤ R0 := hSbound hq
    have hxn : dist x 0 ≤ R0 + 10 * delta := by
      have ht := dist_triangle x q 0
      dsimp [delta]
      rw [hqx] at hx
      linarith
    let y := H.symm x
    have hyx : H y = x := H.apply_symm_apply x
    have hxy : dist x y ≤ rho * h := by simpa only [hyx] using hHd y
    have hyn : ‖y‖ < (B : Real) * h := by
      have ht := dist_triangle y x 0
      rw [dist_comm y x, dist_zero_right y] at ht
      linarith
    rw [hKs]
    refine ⟨y, ?_, hyx⟩
    intro i
    have hi' : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
    exact ⟨by have := (abs_le.mp (hi'.trans hyn.le)).1; linarith,
      (abs_le.mp (hi'.trans hyn.le)).2⟩
  · intro s hsK hsc x hx
    rw [hKf] at hsK
    obtain ⟨t, ht, rfl⟩ := hsK
    obtain ⟨htne, z, pi, _, htsub⟩ := ht
    have htf : Face t := ⟨htne, z, pi, htsub⟩
    have himage : t.image H = t.image f := by
      apply Finset.image_congr
      intro a ha
      obtain ⟨z', rfl⟩ := hvertex htf ha
      exact hHw z'
    have hcard : (t.image H).card = t.card := Finset.card_image_of_injective t H.injective
    rw [hcard] at hsc
    have htclear := hclear t htf (by intro a _ ha; exact ha) hsc x
      (by simpa only [himage] using hx)
    exact (mul_le_mul_of_nonneg_right (hbmono (by omega : t.card - 1 ≤ N - 4))
      hh.le).trans_lt htclear

end Poincare.Topology
