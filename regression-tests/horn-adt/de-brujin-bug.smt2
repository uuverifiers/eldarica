; Case in which we previously produced an incorrect solution due
; to incorrect handling of de Brujin indexes
; Bug #61

(set-logic HORN)

( declare-datatypes ( ( f 0 ) ) ( ( ( g ) ( h ( i Int ) ( j f ) ) ) ) )
( declare-datatypes ( ( d1 0 ) ) ( ( ( b ( c d1 ) ( d111 d1 ) ) ( e ) ) ) )
( declare-fun n ( f ) Bool )
( declare-fun mmin ( f ) Bool )
( declare-fun p ( f d1 f ) Bool )
( assert ( forall ( ( q f ) ) ( => ( and ( mmin q ) ( n q ) ) false ) ) )
( assert ( forall ( ( s f ) ( w d1 ) ( y d1 ) ( z f ) ) ( => ( and ( p s w s ) ( p z y z ) ) ( p s ( b w y ) z ) ) ) )
( assert ( forall ( ( q f ) ) ( p q e q ) ) )
( assert ( forall ( ( q f ) ) ( => ( p q e g ) ( n q ) ) ) )
( assert ( mmin ( h 0 g ) ) )
(check-sat)
