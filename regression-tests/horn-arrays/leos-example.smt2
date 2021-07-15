(set-logic HORN)

(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-fun |interface_C_40_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_C_40_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_C_40_0_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_C_40_1_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_C_40_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_2_function_f__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_C_40_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_2_function_f__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 n_3_0 state_2 n_3_1))) (nondet_interface_C_40_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_3_function_f__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int ) Bool)
(declare-fun |block_4_f_38_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (i_16_0 Int) (i_16_1 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int))
(block_3_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (i_16_0 Int) (i_16_1 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int))
(=> (and (and (block_3_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1) (and (and (and (= state_1 state_0) (= error_0 0)) (= n_3_0 n_3_1)) true)) true) (block_4_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1))))


(declare-fun |block_5_return_function_f__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int ) Bool)
(declare-fun |block_6_for_header_f_31_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int ) Bool)
(declare-fun |block_7_for_body_f_30_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int ) Bool)
(declare-fun |block_8_f_38_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int))
(=> (and (and (block_4_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1) (and (= i_16_2 expr_17_0) (and (=> true true) (and (= expr_17_0 0) (and (=> true expr_9_1) (and (= expr_9_1 (> expr_7_0 expr_8_0)) (and (=> true true) (and (= expr_8_0 0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 n_3_1) (and (and (>= n_3_1 0) (<= n_3_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (= i_16_1 0) (and (= x_13_1 0) true))))))))))))) true) (block_6_for_header_f_31_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int))
(=> (and (and (block_6_for_header_f_31_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1) (and (= expr_21_1 (< expr_19_0 expr_20_0)) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 n_3_1) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 i_16_1) true)))))) expr_21_1) (block_7_for_body_f_30_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int))
(=> (and (and (block_6_for_header_f_31_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1) (and (= expr_21_1 (< expr_19_0 expr_20_0)) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 n_3_1) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 i_16_1) true)))))) (not expr_21_1)) (block_8_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (block_7_for_body_f_30_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1) (and (= i_16_2 (ite (> (+ i_16_1 1) 115792089237316195423570985008687907853269984665640564039457584007913129639935) k_27_0_0 (ite (< (+ i_16_1 1) 0) k_27_0_0 (+ i_16_1 1)))) (and (= expr_27_1 (ite (> (+ i_16_1 1) 115792089237316195423570985008687907853269984665640564039457584007913129639935) k_27_0_0 (ite (< (+ i_16_1 1) 0) k_27_0_0 (+ i_16_1 1)))) (and (<= k_27_0_0 115792089237316195423570985008687907853269984665640564039457584007913129639935) (and (>= k_27_0_0 0) (and (= (+ i_16_1 1) (+ k_27_0_0 (* (+ (+ (- 0 0) 115792089237316195423570985008687907853269984665640564039457584007913129639935) 1) m_27_0_0))) (and (= expr_26_0 i_16_1) (and (= x_13_2 expr_24_1) (and (=> true (and (>= expr_24_1 0) (<= expr_24_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_1 expr_23_0) (and (=> true (and (>= expr_23_0 0) (<= expr_23_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_0 i_16_1) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 x_13_1) true)))))))))))))) true) (block_6_for_header_f_31_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_2 i_16_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (block_8_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1) (and (= expr_35_1 (< expr_33_0 expr_34_0)) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 n_3_1) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_13_1) true)))))) (and (not expr_35_1) (= error_1 1))) (summary_2_function_f__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (block_8_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1) (and (= error_1 error_0) (and (= expr_35_1 (< expr_33_0 expr_34_0)) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 n_3_1) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_13_1) true))))))) true) (block_5_return_function_f__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (block_5_return_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1 x_13_1 i_16_1) true) true) (summary_2_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (interface_C_40_0 this_0 abi_0 crypto_0 state_0) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (= (|msg.sig| tx_0) 3017696395)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 179)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 222)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 100)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 139)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4)) (summary_2_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1)) (= error_0 0))) (interface_C_40_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_entry_C_40_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (= state_1 state_0) (= error_0 0)) (contract_initializer_entry_C_40_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_C_40_10_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (contract_initializer_entry_C_40_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_C_40_10_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (contract_initializer_after_init_C_40_10_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_C_40_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_C_40_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (implicit_constructor_entry_C_40_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (implicit_constructor_entry_C_40_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_C_40_1_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_C_40_0_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (implicit_constructor_entry_C_40_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_C_40_1_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_C_40_0_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (summary_constructor_C_40_0_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (= error_0 0)) (interface_C_40_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_2_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (n_3_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> (and (and (interface_C_40_0 this_0 abi_0 crypto_0 state_0) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (= (|msg.sig| tx_0) 3017696395)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 179)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 222)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 100)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 139)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4)) (summary_2_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 n_3_0 state_1 n_3_1)) (= error_0 1))) error_target_2_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (i_16_0 Int) (i_16_1 Int) (i_16_2 Int) (k_27_0_0 Int) (m_27_0_0 Int) (n_3_0 Int) (n_3_1 Int) (n_3_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_13_0 Int) (x_13_1 Int) (x_13_2 Int))
(=> error_target_2_0 false)))
(check-sat)
(get-model)


