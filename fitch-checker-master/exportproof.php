<?php

if (!(isset($_POST))) {
   return;
}

if (!(isset($_POST["proofData"]))) {
   return;
}

if (!(isset($_POST["numPrems"]))) {
   return;
}

if (!(isset($_POST["wantedConc"]))) {
   return;
}

$pr_data_json = $_POST["proofData"];

$pr_data = json_decode($_POST["proofData"]);

if (json_last_error() != JSON_ERROR_NONE) {
   return;
}

require 'syntax.php';

$predicateSettings = ($_POST["predicateSettings"] == "true") ?? false;

$wantedConc = $_POST["wantedConc"];

$numprems = intval($_POST["numPrems"]);

// Now we've unpacked everything we were 
// sent by p.startExportMe in proofs.js

require 'proofs.php';

// $export_result = export_proof($pr_data, $numprems, $wantedConc);
$curr_line = 0;
$export_result = export_proof($pr_data, $curr_line);
// export_proof is in proofs.php

// Temporarily, let's just send the proof data and see what it looks like [18:53]
echo json_encode($export_result);
// echo json_encode($pr_data);  


exit;
?>