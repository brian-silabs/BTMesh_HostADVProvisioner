/***************************************************************************//**
 * @file
 * @brief Empty BTmesh NCP-host Example Project.
 *******************************************************************************
 * # License
 * <b>Copyright 2021 Silicon Laboratories Inc. www.silabs.com</b>
 *******************************************************************************
 *
 * SPDX-License-Identifier: Zlib
 *
 * The licensor of this software is Silicon Laboratories Inc.
 *
 * This software is provided 'as-is', without any express or implied
 * warranty. In no event will the authors be held liable for any damages
 * arising from the use of this software.
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute it
 * freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must not
 *    claim that you wrote the original software. If you use this software
 *    in a product, an acknowledgment in the product documentation would be
 *    appreciated but is not required.
 * 2. Altered source versions must be plainly marked as such, and must not be
 *    misrepresented as being the original software.
 * 3. This notice may not be removed or altered from any source distribution.
 *
 ******************************************************************************/

/* standard library headers */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <errno.h>
#include "system.h"
#include "sl_bt_api.h"
#include "sl_btmesh_api.h"
#include "sl_btmesh_generic_model_capi_types.h"
#include "sl_btmesh_ncp_host.h"
#include "sl_bt_ncp_host.h"
#include "app_log.h"
#include "app_assert.h"
#include "uart.h"
#include "app.h"
#include "tcp.h"
#include <unistd.h>
#ifdef POSIX
#include "named_socket.h"

#define CLIENT_ENCRYPTED_PATH "client_encrypted"
#define CLIENT_UNENCRYPTED_PATH "client_unencrypted"


#include "vendor_model.h"

/** Usage string for Posix systems */
#define USAGE "\n%s\n"                                                                         \
              "Usage: -u <serial port> <baud rate> [flow control: 1(on, default) or 0(off)]\n" \
              "       -t <IPv4 address (e.g. 192.168.0.0)>\n"                                  \
              "       -n <server_domain_socket> -s (is_domain_socket_encrypted? 0/1)\n\n"
#else
/** Usage string for non-Posix systems */
#define USAGE "\n%s\n"                                                                         \
              "Usage: -u <serial port> <baud rate> [flow control: 1(on, default) or 0(off)]\n" \
              "       -t <IPv4 address (e.g. 192.168.0.0)>\n\n"
#endif
#define DEFAULT_UART_PORT             NULL
#define DEFAULT_UART_BAUD_RATE        115200
#define DEFAULT_UART_FLOW_CONTROL     1
#define DEFAULT_UART_TIMEOUT          100
#define DEFAULT_TCP_PORT              "4901"
#define MAX_OPT_LEN                   255

// This characteristic handle value has to match the value in gatt_db.h of
// NCP empty example running on the connected WSTK.
#define GATTDB_SYSTEM_ID 18

static bool enable_security = false;

// Serail port name of the NCP target
static char uart_target_port[MAX_OPT_LEN];
// IP address or host name of the NCP target using TCP connection
static char tcp_target_address[MAX_OPT_LEN];

#ifdef POSIX
static char named_socket_target_address[MAX_OPT_LEN];
#endif


uint16_t netkey_id = KEY_INDEX_INVALID;//0xfff;
uint16_t appkey_id = KEY_INDEX_INVALID;//0xfff;
uint8_t ask_user_input = false;
uint16_t provisionee_address = ADDRESS_INVALID;//0xFFFF;

uint8_t netkey_buffer[KEY_SIZE_B] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
uint8_t appkey_buffer[KEY_SIZE_B] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};

uint32_t dcd_handle = 0;

uint8_t factory_reset = false;

uint8_t config_retrycount = 0;
#ifdef PROVISION_OVER_GATT
bd_addr             bt_address;
uint8_t               bt_address_type;
#endif

struct mesh_generic_state current, target;

static uint8_t num_connections = 0;     /* number of active Bluetooth connections */
static uint8_t conn_handle = 0xFF;      /* handle of the last opened LE connection */

// DCD content of the last provisioned device. (the example code decodes up to two elements, but
// only the primary element is used in the configuration to simplify the code)
tsDCD_ElemContent _sDCD_Prim;
tsDCD_ElemContent _sDCD_2nd; /* second DCD element is decoded if present, but not used for anything (just informative) */
uint8_t _dcd_raw[256]; // raw content of the DCD received from remote node
uint8_t _dcd_raw_len = 0;
// config data to be sent to last provisioned node:
tsConfig _sConfig;

enum {
  init = 0,
  scanning,
  connecting,
  provisioning,
  provisioned,
  waiting_dcd,
  waiting_appkey_ack,
  waiting_bind_ack,
  waiting_pub_ack,
  waiting_sub_ack
} state;

////////////////// Example specific Data //////////////////////
my_model_t my_model = {
  .elem_index = PRIMARY_ELEMENT,
  .vendor_id = MY_VENDOR_ID,
  .model_id = MY_MODEL_SERVER_ID,
  .publish = 1,
  .opcodes_len = NUMBER_OF_OPCODES,
  .opcodes_data[0] = custom_get,
  .opcodes_data[1] = custom_set};


/*
 * Look-up table for mapping error codes to strings. Not a complete
 * list, for full description of error codes, see
 * Bluetooth LE and Mesh Software API Reference Manual */

tsErrCode _sErrCodes[] = {
    {0x0c01, "already_exists"},
    {0x0c02, "does_not_exist"},
    {0x0c03, "limit_reached"},
    {0x0c04, "invalid_address"},
    {0x0c05, "malformed_data"},
    {0x0181, "wrong_state"},
    {0x0183, "not_implemented"},
    {0x0185, "timeout"},
};

const char err_unknown[] = "<?>";

static int serial_port_init(char* uart_port, uint32_t uart_baud_rate,
                            uint32_t uart_flow_control, int32_t timeout);
static void app_deinit(int cause);
static void uart_tx_wrapper(uint32_t len, uint8_t *data);
static void tcp_tx_wrapper(uint32_t len, uint8_t *data);
static void processTimeout(uint8_t timerHandle);

/***************************************************************************//**
 * This function is called to initiate factory reset. Factory reset may be
 * initiated by keeping one of the WSTK pushbuttons pressed during reboot.
 * Factory reset is also performed if it is requested by the provisioner
 * (event gecko_evt_mesh_node_reset_id).
 ******************************************************************************/
static void initiate_factory_reset(void)
{
  app_log("factory reset\r\n");

  /* if connection is open then close it before rebooting */
  if (conn_handle != 0xFF) {
    sl_bt_connection_close(conn_handle);
  }

  /* perform a factory reset by erasing PS storage. This removes all the keys and other settings
     that have been configured for this node */
  sl_bt_nvm_erase_all();
  // reboot after a small delay
  sl_bt_system_set_soft_timer(2 * 32768, TIMER_ID_FACTORY_RESET, 1);
}

static sl_status_t provisionDeviceOverAdv( uuid_128 aDevice_uuid)
{
  sl_status_t sc = SL_STATUS_OK;
  uint8_t attention_time_seconds = PROVISION_ATTN_TIME_DISABLED;


  sc = sl_btmesh_prov_create_provisioning_session(netkey_id, aDevice_uuid, attention_time_seconds);
  app_assert(sc == SL_STATUS_OK,
          "[E: 0x%04x] Failed to create provisioning session\n",
          (int)sc);

  if(sc == SL_STATUS_OK)
  {
    sc = sl_btmesh_prov_provision_adv_device(aDevice_uuid);
    app_assert(sc == SL_STATUS_OK,
          "[E: 0x%04x] Failed to provision ADV device\n",
          (int)sc);
  }

  return sc;
}

/* function for decoding one element inside the DCD. Parameters:
 *  pElem: pointer to the beginning of element in the raw DCD data
 *  pDest: pointer to a struct where the decoded values are written
 * */
static void DCD_decode_element(tsDCD_Elem *pElem, tsDCD_ElemContent *pDest)
{
  uint16_t *pu16;
  int i;

  memset(pDest, 0, sizeof(*pDest));

  pDest->numSIGModels = pElem->numSIGModels;
  pDest->numVendorModels = pElem->numVendorModels;

  app_log("Num sig models: %d\r\n", pDest->numSIGModels );
  app_log("Num vendor models: %d\r\n", pDest->numVendorModels);

  if(pDest->numSIGModels > MAX_SIG_MODELS)
  {
    app_log("ERROR: number of SIG models in DCD exceeds MAX_SIG_MODELS (%u) limit!\r\n", MAX_SIG_MODELS);
    return;
  }
  if(pDest->numVendorModels > MAX_VENDOR_MODELS)
  {
    app_log("ERROR: number of VENDOR models in DCD exceeds MAX_VENDOR_MODELS (%u) limit!\r\n", MAX_VENDOR_MODELS);
    return;
  }

  // set pointer to the first model:
  pu16 = (uint16_t *)pElem->payload;

  // grab the SIG models from the DCD data
  for(i=0;i<pDest->numSIGModels;i++)
  {
    pDest->SIG_models[i] = *pu16;
    pu16++;
    app_log("model ID: %4.4x\r\n", pDest->SIG_models[i]);
  }

  // grab the vendor models from the DCD data
  for (i = 0; i < pDest->numVendorModels; i++) {
    pDest->vendor_models[i].vendor_id = *pu16;
    pu16++;
    pDest->vendor_models[i].model_id = *pu16;
    pu16++;

    app_log("vendor ID: %4.4X, model ID: %4.4X\r\n", pDest->vendor_models[i].vendor_id, pDest->vendor_models[i].model_id);
  }
}

static void DCD_decode()
{
  tsDCD_Header *pHeader;
  tsDCD_Elem *pElem;
  uint8_t byte_offset;

  pHeader = (tsDCD_Header *)&_dcd_raw;

  app_log("DCD: company ID %4.4X, Product ID %4.4X\r\n", pHeader->companyID, pHeader->productID);

  pElem = (tsDCD_Elem *)pHeader->payload;

  // decode primary element:
  DCD_decode_element(pElem, &_sDCD_Prim);

  // check if DCD has more than one element by calculating where we are currently at the raw
  // DCD array and compare against the total size of the raw DCD:
  byte_offset = 10 + 4 + pElem->numSIGModels * 2 + pElem->numVendorModels * 4; // +10 for DCD header, +4 for header in the DCD element

  if(byte_offset < _dcd_raw_len)
  {
    // set elem pointer to the beginning of 2nd element:
    pElem = (tsDCD_Elem *)&(_dcd_raw[byte_offset]);

    app_log("Decoding 2nd element (just informative, not used for anything)\r\n");
    DCD_decode_element(pElem, &_sDCD_2nd);
  }
}

/*
 * Add one publication setting to the list of configurations to be done
 * */
static void config_pub_add(uint16_t model_id, uint16_t vendor_id, uint16_t address)
{
  _sConfig.pub_model[_sConfig.num_pub].model_id = model_id;
  _sConfig.pub_model[_sConfig.num_pub].vendor_id = vendor_id;
  _sConfig.pub_address[_sConfig.num_pub] = address;
  _sConfig.num_pub++;
}

/*
 * Add one subscription setting to the list of configurations to be done
 * */
static void config_sub_add(uint16_t model_id, uint16_t vendor_id, uint16_t address)
{
  _sConfig.sub_model[_sConfig.num_sub].model_id = model_id;
  _sConfig.sub_model[_sConfig.num_sub].vendor_id = vendor_id;
  _sConfig.sub_address[_sConfig.num_sub] = address;
  _sConfig.num_sub++;
}

/*
 * Add one appkey/model bind setting to the list of configurations to be done
 * */
static void config_bind_add(uint16_t model_id, uint16_t vendor_id, uint16_t netkey_id, uint16_t appkey_id)
{
  _sConfig.bind_model[_sConfig.num_bind].model_id = model_id;
  _sConfig.bind_model[_sConfig.num_bind].vendor_id = vendor_id;
  _sConfig.num_bind++;
}

/*
 * This function scans for the SIG models in the DCD that was read from a freshly provisioned node.
 * Based on the models that are listed, the publish/subscribe addresses are added into a configuration list
 * that is later used to configure the node.
 *
 * This example configures generic on/off client and lightness client to publish
 * to "light control" group address and subscribe to "light status" group address.
 *
 * Similarly, generic on/off server and lightness server (= the light node) models
 * are configured to subscribe to "light control" and publish to "light status" group address.
 *
 * Alternative strategy for automatically filling the configuration data would be to e.g. use the product ID from the DCD.
 *
 * NOTE: this example only checks the primary element of the node. Other elements are ignored.
 * */
static void config_check()
{
  int i;

  memset(&_sConfig, 0, sizeof(_sConfig));

  // scan the SIG models in the DCD data
  for(i=0;i<_sDCD_Prim.numSIGModels;i++)
  {
    // if(_sDCD_Prim.SIG_models[i] == SWITCH_MODEL_ID)
    // {
    //   config_pub_add(SWITCH_MODEL_ID, 0xFFFF, LIGHT_CTRL_GRP_ADDR);
    //   config_sub_add(SWITCH_MODEL_ID, 0xFFFF, LIGHT_STATUS_GRP_ADDR);
    //   config_bind_add(SWITCH_MODEL_ID, 0xFFFF, 0, 0);
    // }
    // else if(_sDCD_Prim.SIG_models[i] == LIGHT_MODEL_ID)
    // {
    //   config_pub_add(LIGHT_MODEL_ID, 0xFFFF, LIGHT_STATUS_GRP_ADDR);
    //   config_sub_add(LIGHT_MODEL_ID, 0xFFFF, LIGHT_CTRL_GRP_ADDR);
    //   config_bind_add(LIGHT_MODEL_ID, 0xFFFF, 0, 0);
    // }
    // else if(_sDCD_Prim.SIG_models[i] == DIM_SWITCH_MODEL_ID)
    // {
    //   config_pub_add(DIM_SWITCH_MODEL_ID, 0xFFFF, LIGHT_CTRL_GRP_ADDR);
    //   config_sub_add(DIM_SWITCH_MODEL_ID, 0xFFFF, LIGHT_STATUS_GRP_ADDR);
    //   config_bind_add(DIM_SWITCH_MODEL_ID, 0xFFFF, 0, 0);
    // }
    // else if(_sDCD_Prim.SIG_models[i] == DIM_LIGHT_MODEL_ID)
    // {
    //   config_pub_add(DIM_LIGHT_MODEL_ID, 0xFFFF, LIGHT_STATUS_GRP_ADDR);
    //   config_sub_add(DIM_LIGHT_MODEL_ID, 0xFFFF, LIGHT_CTRL_GRP_ADDR);
    //   config_bind_add(DIM_LIGHT_MODEL_ID, 0xFFFF, 0, 0);
    // }
  }

#ifdef CONFIGURE_VENDOR_MODEL
  // scan the vendor models found in the DCD
  for(i=0;i<_sDCD_Prim.numVendorModels;i++)
  {
    // this example only handles vendor model with vendor ID 0x02FF (Silabs) and model ID 0xABCD.
    // if such model found, configure it to publish/subscribe to a single group address
    if((_sDCD_Prim.vendor_models[i].model_id == VENDOR_MODEL_ID) && (_sDCD_Prim.vendor_models[i].vendor_id == VENDOR_ID))
    {
      config_pub_add(VENDOR_MODEL_ID, VENDOR_ID, VENDOR_GRP_ADDR);
      config_sub_add(VENDOR_MODEL_ID, VENDOR_ID, VENDOR_GRP_ADDR);
      // using single appkey to bind all models. It could be also possible to use different appkey for the
      // vendor models
      config_bind_add(VENDOR_MODEL_ID, VENDOR_ID, 0, 0);
    }
  }
#endif

}

static void config_retry(uint8_t timer_handle){
  /* maximum number of retry attempts is limited to 5 in this example. If the limit
   * is reached, then there is probably something wrong with the configuration and
   * there is no point to do try again anymore */
  const uint8_t max_retrycount = 5;

  if(config_retrycount > max_retrycount){
    app_log("ERROR: max limit of configuration retries reached\r\n");
  }
  else{
    config_retrycount++;
  }

  app_log(" trying again, attempt %u/%u\r\n", config_retrycount, max_retrycount);
  sl_bt_system_set_soft_timer(TIMER_MS_2_TIMERTICK(500), timer_handle, SOFT_TIMER_REPEATING);
}

static void trigger_next_state(uint8_t timer_handle){
  // when moving to new state in the configuration state machine, the retry counter is cleared:
  config_retrycount = 0;

  sl_bt_system_set_soft_timer(TIMER_MS_2_TIMERTICK(100), timer_handle, 1);
}

/**************************************************************************//**
 * Application Init.
 *****************************************************************************/
void app_init(int argc, char *argv[])
{
  int opt;
  uint32_t target_baud_rate = DEFAULT_UART_BAUD_RATE;
  uint32_t target_flow_control = DEFAULT_UART_FLOW_CONTROL;

  uart_target_port[0] = '\0';
  tcp_target_address[0] = '\0';

  //Parse command line arguments
  while ((opt = getopt(argc, argv, "t:T:u:U:b:B:f:F:n:N:r:R:sShH")) != -1) {
    switch (opt) {
      case 'U':
      case 'u': //Target Uart port or address.
        strncpy(uart_target_port, optarg, MAX_OPT_LEN);
        break;
      case 'T':
      case 't': //Target TCP address
        strncpy(tcp_target_address, optarg, MAX_OPT_LEN);
        break;
      case 'F':
      case 'f': //Target flow control
        target_flow_control = atol(optarg);
        break;
      case 'B':
      case 'b': //Target baud rate
        target_baud_rate = atol(optarg);
        break;
      case 'S':
      case 's':
        enable_security = true;
        break;
      case 'R':
      case 'r': //Factory reset!
        factory_reset = true;
        app_log("Will factory reset provisionner - DB will be lost\n");
        break;
#ifdef POSIX
      case 'N':
      case 'n':
        strncpy(named_socket_target_address, optarg, MAX_OPT_LEN);
        break;
#endif
      case 'H':
      case 'h': //Help!
        app_log(USAGE, argv[0]);
        exit(EXIT_SUCCESS);

      default: /* '?' */
        app_log(USAGE, argv[0]);
        exit(EXIT_FAILURE);
    }
  }
  if (uart_target_port[0] != '\0') {
    // Initialise serial communication as non-blocking.
    SL_BT_API_INITIALIZE_NONBLOCK(uart_tx_wrapper, uartRx, uartRxPeek);
    if (serial_port_init(uart_target_port, target_baud_rate,
                         target_flow_control, DEFAULT_UART_TIMEOUT) < 0) {
      app_log("Non-blocking serial port init failure\n");
      exit(EXIT_FAILURE);
    }
  } else if (tcp_target_address[0] != '\0') {
    // Initialise socket communication
    SL_BT_API_INITIALIZE_NONBLOCK(tcp_tx_wrapper, tcp_rx, tcp_rx_peek);
    if (tcp_open(tcp_target_address, DEFAULT_TCP_PORT) < 0) {
      app_log("Non-blocking TCP connection init failure\n");
      exit(EXIT_FAILURE);
    }
#ifdef POSIX
  } else if (named_socket_target_address[0] != '\0') {
    // Initialise serial communication as non-blocking.
    SL_BT_API_INITIALIZE_NONBLOCK(af_socket_tx, af_socket_rx,
                                  af_socket_rx_peek);
    if (enable_security) {
      if (connect_domain_socket_server(named_socket_target_address,
                                       CLIENT_ENCRYPTED_PATH, 1)) {
        app_log("Connection to encrypted domain socket unsuccessful. Exiting..\n");
        exit(EXIT_FAILURE);
      }
      app_log("Turning on Encryption. All subsequent BGAPI commands and events will be encrypted..\n");
      turn_encryption_on();
    } else {
      if (connect_domain_socket_server(named_socket_target_address,
                                       CLIENT_UNENCRYPTED_PATH, 0)) {
        app_log("Connection to unencrypted domain socket unsuccessful. Exiting..\n");
        exit(EXIT_FAILURE);
      }
    }
#endif
  } else {
    app_log("Either uart port or TCP address shall be given.\n");
    app_log(USAGE, argv[0]);
    exit(EXIT_FAILURE);
  }

  SL_BTMESH_API_REGISTER();

  app_log("Empty NCP-host initialised\n");
  app_log("Resetting NCP...\n");
  // Reset NCP to ensure it gets into a defined state.
  // Once the chip successfully boots, boot event should be received.

  sl_bt_system_reset(0);

  /////////////////////////////////////////////////////////////////////////////
  // Put your additional application init code here!                         //
  // This is called once during start-up.                                    //
  /////////////////////////////////////////////////////////////////////////////
}

/**************************************************************************//**
 * Application Process Action.
 *****************************************************************************/
void app_process_action(void)
{
  /////////////////////////////////////////////////////////////////////////////
  // Put your additional application code here!                              //
  // This is called infinitely.                                              //
  // Do not call blocking functions from here!                               //
  /////////////////////////////////////////////////////////////////////////////

}

/**************************************************************************//**
 * Bluetooth stack event handler.
 * This overrides the dummy weak implementation.
 *
 * @param[in] evt Event coming from the Bluetooth stack.
 *****************************************************************************/
void sl_bt_on_event(sl_bt_msg_t *evt)
{
  sl_status_t sc;

  switch (SL_BT_MSG_ID(evt->header)) {
    // -------------------------------
    // This event indicates the device has started and the radio is ready.
    // Do not call any stack command before receiving this boot event!
    case sl_bt_evt_system_boot_id:

      // Print boot message.
      app_log("Bluetooth stack booted: v%d.%d.%d-b%d\n",
              evt->data.evt_system_boot.major,
              evt->data.evt_system_boot.minor,
              evt->data.evt_system_boot.patch,
              evt->data.evt_system_boot.build);

      // check pushbutton state at startup. If either PB0 or PB1 is held down then do factory reset
      if (factory_reset) {
        initiate_factory_reset();
      } else {
        printf("Initializing as provisioner\r\n");

        state = init;
        // init as provisioner
        sc = sl_btmesh_prov_init();
        app_assert(sc == SL_STATUS_OK,
              "[E: 0x%04x] Failed to init provisioner\n",
              (int)sc);
      }
      break;

    case sl_bt_evt_system_soft_timer_id:
      processTimeout(evt->data.evt_system_soft_timer.handle);
      break;

    ///////////////////////////////////////////////////////////////////////////
    // Add additional event handlers here as your application requires!      //
    ///////////////////////////////////////////////////////////////////////////

    // -------------------------------
    // Default event handler.
    default:
      break;
  }
}

/**************************************************************************//**
 * Bluetooth Mesh stack event handler.
 * This overrides the dummy weak implementation.
 *
 * @param[in] evt Event coming from the Bluetooth Mesh stack.
 *****************************************************************************/
void sl_btmesh_on_event(sl_btmesh_msg_t *evt)
{
  sl_status_t sc;
  size_t appkey_len = 0;
  uint8_t i = 0;

  switch (SL_BT_MSG_ID(evt->header)) {
    case sl_btmesh_evt_prov_initialized_id:
      app_log("Provisioner Initialized\r\n");

      app_log("Networks: %d\r\n", evt->data.evt_prov_initialized.networks);
      app_log("Address: %x\r\n", evt->data.evt_prov_initialized.address);
      app_log("Primary Network IV Index: %x\r\n", evt->data.evt_prov_initialized.iv_index);

      if (evt->data.evt_prov_initialized.networks <= 0) {
        netkey_id = NETWORK_KEY_INDEX;
        app_log("Genrating new random network key at index: %x\r\n", netkey_id);
        sc = sl_btmesh_prov_create_network(netkey_id, 0, (const uint8_t *)"");
        app_assert(sc == SL_STATUS_OK,
              "[E: 0x%04x] Failed to create net key\n",
              (int)sc);
        if(sc == SL_STATUS_OK)
        {
          appkey_id = APPLICATION_KEY_INDEX;
          sc = sl_btmesh_prov_create_appkey(netkey_id, appkey_id, 0, (const uint8_t *)"", KEY_SIZE_B, &appkey_len, appkey_buffer);
          app_assert(sc == SL_STATUS_OK,
                "[E: 0x%04x] Failed to create app key\n",
                (int)sc);

          app_log("Generated a %d bytes app key \r\n", appkey_len);
        }
      } else {
        // The Node is now initialized,
        // start unprovisioned Beaconing using PB-ADV and PB-GATT Bearers
        app_log("Network Exists\r\n");
      }

      app_log("Network Initialized, starting to scan for unprovisioned device beacons\r\n");
      sc = sl_btmesh_prov_scan_unprov_beacons();
      app_assert(sc == SL_STATUS_OK,
                "[E: 0x%04x] Failed to start mesh beacons scanner\n",
                (int)sc);
      
      state = scanning;
      break;

    case sl_btmesh_evt_prov_unprov_beacon_id :

      if(    (state == scanning)//Clean outputs
          && (evt->data.evt_prov_unprov_beacon.bearer == 0))//ADV bearer
      {
        app_log("Found unprovisioned node\r\n");
        app_log("UUID: \r\n");
        for(i=0;i<16;i++)
        {
          app_log("%2.2x", evt->data.evt_prov_unprov_beacon.uuid.data[i]);
        }
        app_log("\r\n");

        app_log("OOB Capabilities: %2X\r\n", evt->data.evt_prov_unprov_beacon.oob_capabilities);
        app_log("URI Hash: %4X\r\n", evt->data.evt_prov_unprov_beacon.uri_hash);
        app_log("Bearer Type: %X\r\n", evt->data.evt_prov_unprov_beacon.bearer);  

        sc = provisionDeviceOverAdv(evt->data.evt_prov_unprov_beacon.uuid);
        if(sc == SL_STATUS_OK){
          state = provisioning;
        }
      }
      break;

    case sl_btmesh_evt_prov_provisioning_failed_id:
      app_log("Provisioning failed. Reason: %2X\r\n", evt->data.evt_prov_provisioning_failed.reason);
      state = scanning;
      break;

    case sl_btmesh_evt_prov_device_provisioned_id:
      state = provisioned;
      app_log("Node successfully provisioned. Address: %4.4X, ", evt->data.evt_prov_device_provisioned.address);
      app_log("UUID 0x");
      for (i = 0; i < 16; i++)
      {
        app_log("%2.2x", evt->data.evt_prov_device_provisioned.uuid.data[i]);
      } 
      app_log("\r\n");

      provisionee_address = evt->data.evt_prov_device_provisioned.address;

      /* kick of next phase which is reading DCD from the newly provisioned node */
      trigger_next_state(TIMER_ID_GET_DCD);
      break;

    case sl_btmesh_evt_config_client_dcd_data_id:
      if(evt->data.evt_config_client_dcd_data.handle == dcd_handle)//working one device at a time
      {
        app_log("DCD data event, received %u bytes\r\n", evt->data.evt_config_client_dcd_data.data.len);
        // copy the data into one large array. the data may come in multiple smaller pieces.
        // the data is not decoded until all DCD events have been received (see below)
        if((_dcd_raw_len + evt->data.evt_config_client_dcd_data.data.len) <= 256)
        {
          memcpy(&(_dcd_raw[_dcd_raw_len]), evt->data.evt_config_client_dcd_data.data.data, evt->data.evt_config_client_dcd_data.data.len);
          _dcd_raw_len += evt->data.evt_config_client_dcd_data.data.len;
        }
      } else {
        app_log("DCD data received for wrong handle\r\n");
      }
      break;

    case sl_btmesh_evt_config_client_dcd_data_end_id:
      if(evt->data.evt_config_client_dcd_data_end.handle == dcd_handle)
      {
        if(evt->data.evt_config_client_dcd_data_end.result == 0)//success
        {
          app_log("DCD data end event. Decoding the data.\r\n");
          DCD_decode();

          // check the desired configuration settings depending on what's in the DCD
          config_check();

          // sanity check: make sure there is at least one application key to be bound to a model
          if(_sConfig.num_bind == 0)
          {
            app_log("ERROR: don't know how to configure this node, no appkey bindings defined\r\n");
            app_log("Configuration Check does not handle node model configuration\r\n");
          }
          else
          {
            // next step : send appkey to device
            trigger_next_state(TIMER_ID_APPKEY_ADD);
          }
        } else {
          app_log("Reading DCD failed with code 0x%X\r\n", evt->data.evt_config_client_dcd_data_end.result);
          // try again:
          config_retry(TIMER_ID_GET_DCD);
        }
      } else {
        app_log("DCD data received for wrong handle\r\n");
      }
      break;

    case sl_btmesh_evt_config_client_appkey_status_id:
      /* This event is created when a response for an add application key or a remove
        * application key request is received, or the request times out.  */
      if(state == waiting_appkey_ack)
      {
        if(evt->data.evt_config_client_appkey_status.result == 0)
        {
          app_log("App Key added\r\n");
          // move to next step which is binding appkey to models
          trigger_next_state(TIMER_ID_APPKEY_BIND);
        }
        else
        {
          app_log("Add appkey failed with code 0x%X \r\n", evt->data.evt_config_client_appkey_status.result);
          // try again:
          config_retry(TIMER_ID_APPKEY_ADD);
        }
      }
      else
      {
        app_log("ERROR: unexpected appkey status event? (state = %u)\r\n", state);
      }
      break;

    case sl_btmesh_evt_config_client_binding_status_id:
      /* Status event for binding and unbinding application keys and models. */
      if(state == waiting_bind_ack)
      {
        if(evt->data.evt_config_client_binding_status.result == 0)
        {
          app_log("Bind complete\r\n");
          _sConfig.num_bind_done++;

          if(_sConfig.num_bind_done < _sConfig.num_bind)
          {
            // more model<->appkey bindings to be done
            app_log("Performing next model<->appkey binding\r\n");
            trigger_next_state(TIMER_ID_APPKEY_BIND);
          }
          else
          {
            // move to next step which is configuring publish settings
            trigger_next_state(TIMER_ID_PUB_SET);
          }
        }
        else
        {
          app_log(" appkey bind failed with code 0x%X\r\n", evt->data.evt_config_client_binding_status.result);
          // try again:
          config_retry(TIMER_ID_APPKEY_BIND);
        }
      } else {
        app_log("ERROR: unexpected binding status event? (state = %u)\r\n", state);
      }
      break;

    case sl_btmesh_evt_config_client_model_pub_status_id:
      /*Status event for get model publication state, set model publication state, commands. */
      if(state == waiting_pub_ack)
      {
        if(evt->data.evt_config_client_model_pub_status.result == 0)
        {
          app_log("Pub set OK\r\n");
          _sConfig.num_pub_done++;
          if(_sConfig.num_pub_done < _sConfig.num_pub)
          {
            app_log("More publication settings to be done\r\n");
            // more publication settings to be done
            trigger_next_state(TIMER_ID_PUB_SET);
          }
          else
          {
            // move to next step which is configuring subscription settings
            trigger_next_state(TIMER_ID_SUB_ADD);
          }
        }
        else
        {
          printf("Setting pub failed with code 0x%x \r\n", evt->data.evt_config_client_model_pub_status.result);
          // try again:
          config_retry(TIMER_ID_PUB_SET);
        }
      }
      else
      {
        app_log("ERROR: unexpected pub status event? (state = %u)\r\n", state);
      }
      break;

      case sl_btmesh_evt_config_client_model_sub_status_id:
        /* status event for subscription changes */
        if(state == waiting_sub_ack)
        {
          
          if(evt->data.evt_config_client_model_sub_status.result == 0)
          {
            app_log("Sub add OK\r\n");
            _sConfig.num_sub_done++;
            if(_sConfig.num_sub_done < _sConfig.num_sub)
            {
              // more subscription settings to be done
              app_log("More subscription settings to be done\r\n");
              trigger_next_state(TIMER_ID_SUB_ADD);
            }
            else
            {
              app_log("***\r\nconfiguration complete\r\n***\r\n");
              state = scanning;
            }
          }
          else
          {
            app_log("Setting sub failed with code 0x%x \r\n", evt->data.evt_config_client_model_sub_status.result);
            // try again:
            config_retry(TIMER_ID_SUB_ADD);
          }
        }
        else
        {
          app_log("ERROR: unexpected sub status event? (state = %u)\r\n", state);
        }

        break;
    ///////////////////////////////////////////////////////////////////////////
    // Add additional event handlers here as your application requires!      //
    ///////////////////////////////////////////////////////////////////////////

    // -------------------------------
    // Default event handler.
    default:
      break;
  }
}

/**************************************************************************//**
 * UART TX Wrapper.
 *****************************************************************************/
static void uart_tx_wrapper(uint32_t len, uint8_t *data)
{
  if (0 > uartTx(len, data)) {
    app_log("Failed to write to serial port\n");
    app_deinit(0);
    exit(EXIT_FAILURE);
  }
}

/**************************************************************************//**
 * TCP TX Wrapper.
 *****************************************************************************/
static void tcp_tx_wrapper(uint32_t len, uint8_t *data)
{
  if (0 > tcp_tx(len, data)) {
    app_log("Failed to write to TCP port\n");
    app_deinit(0);
    exit(EXIT_FAILURE);
  }
}

/**************************************************************************//**
 * Initialise serial port.
 *****************************************************************************/
static int serial_port_init(char* uart_port, uint32_t uart_baud_rate,
                            uint32_t uart_flow_control, int32_t timeout)
{
  int ret;

  // Sanity check of arguments.
  if (!uart_port || !uart_baud_rate || (uart_flow_control > 1)) {
    app_log("Serial port setting error.\n");
    ret = -1;
  } else {
    // Initialise the serial port.
    ret = uartOpen((int8_t*)uart_port, uart_baud_rate, uart_flow_control, timeout);
  }

  return ret;
}

void app_deinit(int cause)
{
  (void)cause;
  app_log("Shutting down.\n");
  if (uart_target_port[0] != '\0') {
    uartClose();
  } else if (tcp_target_address[0] != '\0') {
    tcp_close();
  }
}

static void processTimeout(uint8_t timerHandle)
{

sl_status_t     sc;
uint32_t        request_handle = 0;
uint16_t        vendor_id;
uint16_t        model_id;
uint16_t        pub_address;
uint16_t        sub_address;

  switch (timerHandle) {

    case TIMER_ID_GET_DCD:
      // clear the old DCD from memory before requesting new one:
      _dcd_raw_len = 0;
      sc = sl_btmesh_config_client_get_dcd(netkey_id, provisionee_address, PAGE0, &dcd_handle);

      if(sc == SL_STATUS_OK)
      {
        app_log("Requesting DCD from the node...\r\n");
        state = waiting_dcd;
      } else {
        app_log("[E: 0x%04x] Failed to request DCD\n",(int)sc);
        sl_bt_system_set_soft_timer(TIMER_MS_2_TIMERTICK(1000), TIMER_ID_GET_DCD, SOFT_TIMER_REPEATING);
      }
      break;

    case TIMER_ID_APPKEY_ADD:
      sc = sl_btmesh_config_client_add_appkey(netkey_id, provisionee_address, appkey_id, netkey_id, &request_handle);
      if (sc == SL_STATUS_OK) 
      {
        app_log("Deploying appkey to node 0x%4.4x\r\n", provisionee_address);
        state = waiting_appkey_ack;
      }else{
        app_log("Appkey deployment failed. addr %x, [E: 0x%04x]\r\n", provisionee_address, sc);
        // try again:
        config_retry(TIMER_ID_APPKEY_ADD);
      }
      break;

    case TIMER_ID_APPKEY_BIND:
      // take the next model from the list of models to be bound with application key.
      // for simplicity, the same appkey is used for all models but it is possible to also use several appkeys
      model_id = _sConfig.bind_model[_sConfig.num_bind_done].model_id;
      vendor_id = _sConfig.bind_model[_sConfig.num_bind_done].vendor_id;

      app_log("APP BIND, config %d/%d:: model %4.4X key index %x\r\n", _sConfig.num_bind_done+1, _sConfig.num_bind, model_id, appkey_id);
      sc = sl_btmesh_config_client_bind_model(netkey_id, provisionee_address, ELEMENT(0), vendor_id, model_id, appkey_id, &request_handle);

      if(sc == SL_STATUS_OK)
      {
        app_log("Waiting bind ack\r\n");
        state = waiting_bind_ack;
      }
      else 
      {
        app_log("sl_btmesh_cmd_config_client_bind_model failed with result 0x%X\r\n", sc);
        // try again:
        config_retry(TIMER_ID_APPKEY_BIND);
      }
      break;

    case TIMER_ID_PUB_SET:
      // get the next model/address pair from the configuration list:
      model_id = _sConfig.pub_model[_sConfig.num_pub_done].model_id;
      vendor_id = _sConfig.pub_model[_sConfig.num_pub_done].vendor_id;
      pub_address = _sConfig.pub_address[_sConfig.num_pub_done];

      app_log("PUB SET, config %d/%d: model %4.4X -> address %4.4X\r\n", _sConfig.num_pub_done+1, _sConfig.num_pub, model_id, pub_address);

      sc = sl_btmesh_config_client_set_model_pub( netkey_id,
                                                  provisionee_address,
                                                  ELEMENT(0),
                                                  vendor_id,
                                                  model_id,
                                                  pub_address,
                                                  appkey_id,
                                                  FRIENDSHIP_CREDENTIALS_NONE,//0, /* friendship credential flag */
                                                  PUB_TTL,//3, /* Publication time-to-live value */
                                                  PUB_PERIOD_MS,//0, /* period = NONE */
                                                  PUB_RETRANS_COUNT,//0, /* Publication retransmission count */
                                                  PUB_RETRANS_INTERVAL_MS,//50  /* Publication retransmission interval */
                                                  &request_handle);
                                                  

      if (sc == SL_STATUS_OK)
      {
        app_log("Waiting pub ack\r\n");
        state = waiting_pub_ack;
      }
      else 
      {
        printf("sl_btmesh_config_client_set_model_pub failed with result 0x%X\r\n", sc);
        config_retry(TIMER_ID_PUB_SET);
      }
      break;

    case TIMER_ID_SUB_ADD:
      // get the next model/address pair from the configuration list:
      model_id = _sConfig.sub_model[_sConfig.num_sub_done].model_id;
      vendor_id = _sConfig.sub_model[_sConfig.num_sub_done].vendor_id;
      sub_address = _sConfig.sub_address[_sConfig.num_sub_done];

      printf("SUB ADD, config %d/%d: model %4.4x -> address %4.4x\r\n", _sConfig.num_sub_done+1, _sConfig.num_sub, model_id, sub_address);

      sc = sl_btmesh_config_client_add_model_sub( netkey_id,
                                                  provisionee_address,
                                                  ELEMENT(0),
                                                  vendor_id,
                                                  model_id,
                                                  sub_address,
                                                  &request_handle);

      if (sc == SL_STATUS_OK)
      {
        printf(" waiting sub ack\r\n");
        state = waiting_sub_ack;
      } else {
        printf("gecko_cmd_mesh_config_client_add_model_sub failed with result 0x%X\r\n", sc);
        config_retry(TIMER_ID_SUB_ADD);
      }
      break;

      case TIMER_ID_FACTORY_RESET:
        sl_bt_system_reset(0);
        break;

      case TIMER_ID_RESTART:
        sl_bt_system_reset(0);
        break;

      default:
        break;
    }

}