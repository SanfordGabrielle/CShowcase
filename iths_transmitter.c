/*
 * iths_transmitter.c - creates beacons and forwards iths messages from Bluetooth over WSMP.
*
********************************************************************************************************
* Copyright ï¿½ Sanford Gabrielle, Ed Hall, Nicolas McMahon, Phil Pfeiffer
* All Rights Reserved
*
* You may use, distribute and modify this code under the terms of the XYZ license.
*
* You should have received a copy of the XYZ license with this file.
* If not, please write to: , or visit :
********************************************************************************************************
*
* Inputs:
*
*  -.  command line parameters:  Invoke this program as
*
*          iths_relay [sch channel access <0 - alternating> <1 - continuous>] [TA channel ] [ TA channel interval <1- cch int> <2- sch int>]
*
*     where
*       ~ sch - WSMP service channel    provide brief description, noting legal values
*       ~ channel - can either be alternating (0) or continuous (1)  meaning what?
*       ~ TA - "timing advertisement" channel  provide brief description, noting legal values
*       ~ cch - "control channel",  provide brief description, noting legal values
*
* - configuration file parameters: XYZ
*
* - standard input: XYZ
*
* Outputs:
*
*  -.  final status codes:
*
*  -.  standard output:
*
*  -.  standard error:
*
* Effects:
*
*   - transmits packets to other device. More notes here to come.
*   - receives messages, including control messages and ITHS messages

*-------------------------------------------------------------------------------------------------------------------
* Design notes:
*
* #. Naming conventions
*.  - WME ("Wave Management Entity") - XYZ
*.  - WSM ("Wave Short Message") - XYZ
*
* The WSM protocol
*
* For more on WSM and the protocol's requirements, see
*   https:// www.researchgate.net/file.PostFileLoader.html?id=562f1f0a60614b71168b45c7&assetKey=AS%3A289060133326849%401445928714746
*
*-------------------------------------------------------------------------------------------------------------------
* Last updated: September 2017
* Current implementation status:  Some last configuration items need to be defined according to the IEEE 1609.0-4 standards.
*
*-------------------------------------------------------------------------------------------------------------------
*/

/* ============== includes ========================
*
* - <signal.h> - for catching SIGINT, SIGTERM, and SIGQUIT
* - <sys/socket.h>, <netinet/in.h>, <netdb.h> - Internet communication, including sockets, protocols
* - wave.h - WSMP primitives; vendor-specific
* - gpsc_probe.h - GPS access
* - configreader.h - provides the struct and method prototype/headers needed for reading from configuration file (readConfigFile)
* @TODO@ add documentation for all of these includes - make sure it's in order (should not what each lib is doing in this file not generic comment)
*/
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <termio.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/ioctl.h>
#include <time.h>
#include <signal.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdbool.h>
#include <errno.h>
#include "wave.h"
#include "gpsc_probe.h"
#include "configreader.h"
// bluetooth-related includes
#include <sys/socket.h>
#include "bluetooth/bluetooth.h"
#include "bluetooth/sdp.h"
#include "bluetooth/sdp_lib.h"
#include "bluetooth/rfcomm.h"



/* ********************** misc. constants *************
*
* Notes:
* -.  APP_PSID - a provider service ID for internal use
* -. FROM_RSU_TOKEN - the token indicating a message is from an RSU
* -.  DEFAULT_IP - default for calling gpsc_probe_connect()
*
*  @TODO@  APP_PSID, currently a #define, needs to be set as a configuration item
*  @TODO@  The usleep() in transmit_packet needs to have its rest time as a config item
*/

#define APP_PSID 52
#define FROM_RSU_TOKEN "FRSU:"
#define FROM_RSU_TOKEN_LEN strlen(FROM_RSU_TOKEN)
#define OCCUPANCY_CHANGE_TOKEN "OCCUPANCY:"
#define OCCUPANCY_CHANGE_TOKEN_LEN strlen(OCCUPANCY_CHANGE_TOKEN)
#define DUTY_CHANGE_TOKEN "DUTY:"
#define DUTY_CHANGE_TOKEN_LEN strlen(DUTY_CHANGE_TOKEN)
#define DEFAULT_IP "127.0.0.1"
#define PAYLOAD_BUFFER_SIZE 512

// bluetooth related constants
#define READ_BUFFER_SIZE 1024   // the buffer size to read in bluetooth messages


/* *** ============== vendor WAVE Communication Primitives ============== *** */

/* *** File scope variables for vendor WAVE Communication Primitives ***
*
* All of these variables need to be protected by mutex's or semaphores
*
* wreq              data for making requests; built by buildWMEApplicationRequest
* entry             instance of a struct for retrieving data on a single service provider; built by buildPSTEntry
* rxpkt             buffer for holding a complete received packet
* pid               provider ID
* wsmreq            holds the contents of a wave request - a wave short message
* wsmControl        holds the contents of a wave control message
* macaddr           current device's MAC address
* occupancyStatus   Whether or not the taxi is occupied. Defaults to true.
* dutyStatus        Whether or not the driver is on-duty. Defaults to true.
*/

static WMEApplicationRequest wreq;   // used in multiple threads
static WMEApplicationRequest entry;  // used in multiple threads
static WSMIndication rxpkt;          // used in multiple threads, controlled by mutex locks[0] and semaphore stopLight[0]
static int pid;                      // used in multiple threads
static WSMRequest wsmBeacon;         // used in multiple threads, holds formatted WSM
static WSMRequest wsmControl;
static char macaddr[32];             // used in multiple threads
static bool occupancyStatus;         // used in multiple threads
static bool dutyStatus;              // used in multiple threads

/* *** ============== CONFIGURATION ITEMS ============== ***
* @TODO@ - need better comment header style here, maybe..
* @TODO@ - fix the comments at the end of the config items
* @TODO@ - create better names for the config variables?
* @TODO@ - APP_PSID, DEFAULT_IP, AND PAYLOAD_BUFFER_SIZE #define's above should possibly be config items as well
*/

static WMEApplicationRequest configAppRequest;
static WSMRequest configWSMRequest;
static WMETARequest configWMETARequest;


// the configuration items
static iths_configuration CONFIG;

/*
 * ================= Bluetooth related variables ==================================
 * BLUETOOTH_PORT  The RFCOMM channel to use for reading messages FROM the phone
 *                 Should never be changed by the program, but does not have a
 *                 const declaration due to being addressed by a pointer later
 *
 * bluetooth_sock       The socket used for reading from the port. Declared globally
 *                 because threads.
 *
 * bluetooth_client     The client used for writing to the phone. Global because threads
 *                 -1 denotes no client connection.
 *
 * bluetooth_rem_addr   The address of the device that connects to the read socket.
 *                 Global because threads.
 *
 * buffer          A weird remnant of Salman's code. No reason to be a global,
 *                 really - the references to it could easily be local. Most have
 *                 been changed, tho it's still used to display connected bluetooth
 *                 address. @TODO@ de-magify this value, and make it local in the
 *                 places it's used (note: some functions use a function scope
 *                 variable of the same name. Those shouldn't be changed)
 *
 * opt             The size of a sockaddr_rc struct. Another weird remnant of salman
 *                 code - at least regarding the naming and globalization of it.
 *                 @TODO@ consider revising this variable and its uses.
 *
 */
static int BLUETOOTH_PORT      = 5;
static int bluetooth_sock, bluetooth_client = -1;
static struct sockaddr_rc bluetooth_rem_addr = { 0 };
char buffer[1024] = { 0 };
static socklen_t opt = sizeof(bluetooth_rem_addr);

/* *** prototypes for vendor WAVE communication primitives ***
*
* buildPSTEntry                     creates an entry in the provider service table
* buildWSMRequestPacket             assigns values to WAVE short message field
* buildWMEApplicationRequest        assigns values to WAVE ....
* buildWMETARequest                 assigns values to WAVE ....
* register_server                   Open-source function from Salman's code-base that
*                                   registers an RFCOMM server. May or may not be entirely
*
*/
int buildPSTEntry(uint8_t channelAccess);
void buildWSMRequestPacket(WSMRequest *request);
void buildWMEApplicationRequest();
void buildWMETARequest(WMETARequest *tareq, uint8_t channel, uint8_t channelInterval);
sdp_session_t *register_service(uint8_t rfcomm_channel);


/* *** ======= application-specific file scope entities ============ *** */

/* *** application-specific data *** ***
*
* rx_packets, tx_packets, drops -    for accumulating transmission statistics
* rx_packets controlled by locks[1], tx_packets controlled by locks[2], drops controlled by locks[3]
*
* @TODO@ port number, serverIP need to be set by remote configuration in final implementation
*/
static uint64_t rx_packets = 0, tx_packets = 0, drops = 0;
static pthread_mutex_t locks[10]; // mutex for all static globals used by multiple threads
static sem_t stopLight[10]; // semaphores to coordinate access to globals


/* *** prototypes for application-specific functions ***
*
*  --- signal catching primitives ---
*
* sig_int -              SIGINT (^C) handler
* sig_term -             SIGTERM handler
* siq_quit -             SIGQUIT (^K) handler
*
*  -- other ---
*/

void sig_int(void);
void sig_term(void);
void sig_quit(void);


/* ***********************************************************
*  iths_transmitter.c codes start here
* ***********************************************************
*/

/* ==========================================================================
*  signal handlers - provide for graceful exit on external interruption
*  ==========================================================================
*/

/* ----------------------------------------------------------------------------------
* program_termination - terminates the program effectively
*
* Inputs:
* -. terminated_by - string characterizing cause of program termination
* -. pid - current process's provider ID
* -. pEntry - address of an instance of a struct for retrieving data on a single service provider
* -. tx_packets - count of packets sent since service start
* -. rx_packets - count of packets received since service start
* -. drops - count of packets dropped since service start
* Outputs: none
* Effects: shuts down program operation, reports transmission statistics, exits
* Design notes:
* -----------------------------------------------------------------------------------
*/
void program_termination(char *terminator, int pid, WMEApplicationRequest *pEntry, uint64_t tx_packets, uint64_t rx_packets, uint64_t drops)
{
  stopWBSS(pid, pEntry);  // halt the WAVE basic service set - i.e., the wireless LAN service
  removeProvider(pid, pEntry);  // stop the provider
  signal(SIGINT,SIG_DFL);
  printf("\n\nPackets Sent = %llu\n", tx_packets);  // report the amount of packets sent
  printf("\nPackets Received = %llu\n", rx_packets);  // report the amount of packets received
  printf("\nPackets Dropped = %llu\n", drops);  // report the number of packets dropped
  printf("\niths_relay killed by %s\n", terminator);
  exit(0);
}

/* ----------------------------------------------------------------------------------
* sig_int - trap SIGINT; includes ^C issued at keyboard
*
* Inputs: none
* Outputs: none
* Effects: calls program_termination to handle terminating the program
* -----------------------------------------------------------------------------------
*/
void sig_int(void)
{
  program_termination("SIGINT", pid, &entry, tx_packets, rx_packets, drops);
}

/* ----------------------------------------------------------------------------------
* sig_term - trap SIGTERM
*
* Inputs: none
* Outputs: none
* Effects: calls program_termination to handle terminating the program
* -----------------------------------------------------------------------------------
*/
void sig_term(void)
{
  program_termination("SIGTERM", pid, &entry, tx_packets, rx_packets, drops);
}

/* ----------------------------------------------------------------------------------
* sig_quit - trap SIGQUIT
*
* Inputs: none
* Outputs: none
* Effects: calls program_termination to handle terminating the program
* -----------------------------------------------------------------------------------
*/
void sig_quit(void)
{
  program_termination("SIGQUIT", pid, &entry, tx_packets, rx_packets, drops);
}

/* ==========================================================================
*  communications buffer processing
*  ==========================================================================
*/

/* ----------------------------------------------------------------------------------
* setControlPacketData - sets the data for a control packet - BUT WHY??
*
* Inputs:   WSMRequest *request - this gets passed in from main
* Outputs:  none
* Effects:  -.  sets up contents of wsmControl, a control packet
*           -.  clears the Data buffer
*
* @TODO@ Find out what the default settings used in buildWSMRequestPacket mean and if they are right
* @TODO@ Eliminate the debugging information
* @TODO@ Set the payload for something useful (heartbeat?)
* -----------------------------------------------------------------------------------
*/
void setControlPacketData()
{
  uint16_t payloadLength = PAYLOAD_BUFFER_SIZE;
  char Data[PAYLOAD_BUFFER_SIZE];
  buildWSMRequestPacket(&wsmControl);  // set the control packet parameters to default

  // Data field is unnecessary in the control packet, leave for now for debugging
  strcpy(Data, "\n<CONTROL>\n");
  strcat(Data, "\t<ORIGIN>");
  strcat(Data, macaddr);  // add the origin device MAC address to the control packet
  strcat(Data, "</ORIGIN>\n");
  strcat(Data, "</CONTROL>\n");
  payloadLength = strlen(Data);
  memcpy ( &wsmControl.data.length, &payloadLength, sizeof(uint16_t));  // copy data and length values into wsmControl
  memcpy ( &wsmControl.data.contents, Data, sizeof (char) * payloadLength);

  strcpy(Data, "");  // clear the payload string
}

/* ----------------------------------------------------------------------------------
* setBeaconPacketData - creates a payload with current GPS data and origin identifier (currently just MAC address)
*
* Inputs:   none
* Outputs:  none
* Effects:  -.  sets up contents of wsmreq, a request packet
*           -.  populates, then clears, the Data buffer
*
* @TODO@ Add the rest of the necessary fields for a beacon - Add the field for ITHS endpoint payload & mechanism to insert
* -----------------------------------------------------------------------------------
*/
void setBeaconPacketData()
{
  uint16_t payloadLength = PAYLOAD_BUFFER_SIZE;     //serves as the payload size var
  char Data[PAYLOAD_BUFFER_SIZE];
  char doubleToStringBuffer[50];
  GPSData gpscReadGPSData;

  // Get the GPS Data -->see LocomateProgrammersGuide 1.4.8
  get_gps_status(&gpscReadGPSData, DEFAULT_IP);  // uses a function in gpsc_probe that encapsulates the method detailed above
  // format the GPS data as strings with XML tags
  strcat(Data, "{ ");
	strcat(Data, "\"time\":");
  // convert time (local Unix time) to string and add to output
  sprintf(doubleToStringBuffer,"%f",gpscReadGPSData.local_tod);
  strcat(Data, doubleToStringBuffer);
	strcat(Data, ",");

	strcat(Data, "\"latitude\":");
  // convert latitude (dd.mmssss) to string and add to output
  sprintf(doubleToStringBuffer,"%f",gpscReadGPSData.latitude);
  strcat(Data, doubleToStringBuffer);
	strcat(Data, ",");

	strcat(Data, "\"latitude_direction\":\"");
  // format latitude direction (N or S) and add to output
  sprintf(doubleToStringBuffer,"%c",gpscReadGPSData.latdir);
  strcat(Data, doubleToStringBuffer);
	strcat(Data, "\",");

	strcat(Data, "\"longitude\":");
  // convert longitude (ddd.mmssss) to string and add to output
  sprintf(doubleToStringBuffer,"%f",gpscReadGPSData.longitude);
  strcat(Data, doubleToStringBuffer);
	strcat(Data, ",");

	strcat(Data, "\"longitude_direction\":\"");
  // format longitude direction (E or W) and add to output
  sprintf(doubleToStringBuffer,"%c",gpscReadGPSData.longdir);
  strcat(Data, doubleToStringBuffer);
	strcat(Data, "\",");

	strcat(Data, "\"altitude\":");
  // convert altitude to string and add to output
  sprintf(doubleToStringBuffer,"%f",gpscReadGPSData.altitude);
  strcat(Data, doubleToStringBuffer);
	strcat(Data, ",");

	strcat(Data, "\"altitude_unit\":\"");
  // format altitude (M meters or F feet) units and add to output
  sprintf(doubleToStringBuffer,"%c",gpscReadGPSData.altunit);     //@TODO@ - this does not return an altitude unit
  strcat(Data, doubleToStringBuffer);
	strcat(Data, "\",");

	strcat(Data, "\"course\":");
  // convert course heading (compass bearing in degrees) to string and add to output
  sprintf(doubleToStringBuffer,"%f",gpscReadGPSData.course);
  strcat(Data, doubleToStringBuffer);
	strcat(Data, ",");

	strcat(Data, "\"speed\":");
  // convert speed to string and add to output
  sprintf(doubleToStringBuffer,"%f",gpscReadGPSData.speed);
  strcat(Data, doubleToStringBuffer);
	strcat(Data, ",");

	strcat(Data, "\"climb\":");
  // convert climb rate (rate of ascent) to string and add to output
  sprintf(doubleToStringBuffer,"%f",gpscReadGPSData.climb);
  strcat(Data, doubleToStringBuffer);

	strcat(Data, ",");

	strcat(Data, "\"sender_mac\":\"");
  strcat(Data, macaddr);
	strcat(Data, "\",");

	strcat(Data, "\"origin_uid\":\"");
  strcat(Data, CONFIG.uid);
	strcat(Data, "\",");

	strcat(Data, "\"duty_status\":\"");
  sprintf(doubleToStringBuffer,"%d", dutyStatus);
  strcat(Data, doubleToStringBuffer);
	strcat(Data, "\",");

	strcat(Data, "\"occupancy_status\":\"");
  sprintf(doubleToStringBuffer,"%d", occupancyStatus);
  strcat(Data, doubleToStringBuffer);
	strcat(Data, "\",");

	strcat(Data, "\"iths_payload\": \"");
	strcat(Data, "ITHS_PAYLOAD_TO_GO_HERE"); //@TODO@ insert the payload here.
	strcat(Data, "\"");

	strcat(Data, "}\n");

  // get the length of Data
  payloadLength = strlen(Data);
  // move Data into the packet payload
  memcpy ( &wsmBeacon.data.length, &payloadLength, sizeof(uint16_t));
  memcpy ( &wsmBeacon.data.contents, Data, sizeof (char) * payloadLength);
  // clear the payload string
  strcpy(Data, "");
}

/* ----------------------------------------------------------------------------------
* buildPSTEntry - build an entry for the provider service table
*
* Inputs:    argv - the rxtx.c command line
* Outputs:   1 if update succeeded, else -1
*
* Effect:   -.  updates global entry data structure
*
* @TODO@ pass values of priority, channel, and repeatrate as parameters, validating them on entry - note: need configuration to do this
* ------------------------------------------------------------------------------------
*/
int buildPSTEntry(uint8_t channelAccess)
{
  entry.psid = CONFIG.WSMRequest_PSID;                            // PSID - Provider Service identifier - see 1609_0 p.17
  entry.priority = CONFIG.WMEApplicationRequest_Priority;         // priority 1 is priority "high", see 1609_1 pp. 23, 55 .from 1609_0 p.15 - "A priority level assigned to a packet that is ready for transmission, which determines its treatment at the medium access control (MAC) layer.", talked about even more on pp.51-50 of 1609_0
  entry.channel = CONFIG.WMEApplicationRequest_Channel;           // from 1609_0 p.30 - "Channels 172, 174, 176, 180, 182, and 184 are service channels (SCH)."
  entry.repeatrate = CONFIG.WMEApplicationRequest_Repeatrate;     // Set to the Repeat Rate of the triggering WME-Timing AdvertisementService.request. Additional information below
                                                                  // repeatrate = 50 per 5 seconds = 1Hz. Tx 1 packet per 100ms (straight from EasyStartGuide_AppDev_AradaSDK.pdf, p.10)

  entry.repeats = CONFIG.WMEApplicationRequest_Repeatrate;        // not mentioned in IEEE (ISA) 1609.0-1609.4
  entry.persistence = CONFIG.WMEApplicationRequest_Persistence;   // not mentioned in IEEE (ISA) 1609.0-1609.4
  entry.userreqtype = USER_REQ_SCH_ACCESS_AUTO;                   // not mentioned in IEEE (ISA) 1609.0-1609.4
  entry.schaccess = CONFIG.WMEApplicationRequest_SCHAccess;       // not mentioned in IEEE (ISA) 1609.0-1609.4, note however - from 1609_0 p.15 - service channel (SCH) is any channel that is not the control channel
  entry.schextaccess = CONFIG.WMEApplicationRequest_SCHEXTAccess; // not mentioned in IEEE (ISA) 1609.0-1609.4
  entry.channelaccess = channelAccess > 1 ? 0 : channelAccess;

  if (channelAccess > 1) printf("channel access set default to alternating access\n");
  return 1;}

/* ----------------------------------------------------------------------------------
* buildWSMRequestPacket - WSMRequest fields to defaults
*
* Inputs:    *request - address of a packet to update
* Outputs:   1 if build succeeded, else -1
*
* Effect:   -.  updates request data structure
*
* @TODO@ document rate, txpower, version
* @TODO@ pass priority, channel, rate, txpower, security, psid, and txpriority as parameters, validating them on entry - note: need configuration to do this
* @TODO@ Make this method validate parameters and return a status code (-1, or 1)
* ------------------------------------------------------------------------------------
*/
void buildWSMRequestPacket(WSMRequest *request)
{
  request->chaninfo.channel = CONFIG.WSMRequest_ChanInfo_Channel; // from 1609_0 p.30 - "Channels 172, 174, 176, 180, 182, and 184 are service channels (SCH).""
  request->chaninfo.rate = CONFIG.WSMRequest_ChanInfo_Rate;       // not mentioned in IEEE (ISA) 1609.0-1609.4
  request->chaninfo.txpower = CONFIG.WSMRequest_ChanInfo_TXPower; // not defined in IEEE (ISA) 1609.0-1609.4
  request->version = CONFIG.WSMRequest_Version;                   // not mentioned in IEEE (ISA) 1609.0-1609.4
  request->security = CONFIG.WSMRequest_Security;                 // unsecured --?? @TODO@  define further
  request->psid = CONFIG.WSMRequest_PSID;                         // PSID - Provider Service identifier - see 1609_0 p.17
  request->txpriority = CONFIG.WSMRequest_TXPriority;             // not mentioned in IEEE (ISA) 1609.0-1609.4

  memset ( &(*request).data, 0, sizeof( WSMData));    // zero out data field
}

/* ----------------------------------------------------------------------------------
* buildWMETARequest - WSMRequest fields to defaults
*
* Inputs:    uint8_t channel
*            uint8_t channelInterval
* Outputs:   1 if build succeeded, else -1
*
* Effect:    updates global tareq data structure
*
* @TODO@ document action, repeatrate, channel, channelinterval, and servicepriority
* @TODO@ pass action, repeatrate, channel, channelinterval, and servicepriority as parameters, validating them on entry - note: need configuration to do this
* @TODO@ Make this method validate parameters and return a status code (-1, or 1)
* ------------------------------------------------------------------------------------
*/
void buildWMETARequest(WMETARequest *tareq, uint8_t channel, uint8_t channelInterval)
{
  tareq->action = TA_ADD;                      // See 1609_2 p.53 -  I believe the actions are defined here
  tareq->repeatrate = CONFIG.WMETARequest_RepeatRate;                     // Set to the Repeat Rate of the triggering WME-Timing AdvertisementService.request. Additional information below
  tareq->channel = channel;                    // from 1609_0 p.30 - "Channels 172, 174, 176, 180, 182, and 184 are service channels (SCH)."
  tareq->channelinterval = channelInterval;    // not mentioned in IEEE (ISA) 1609.0-1609.4
  tareq->servicepriority = CONFIG.WMETARequest_ServicePriority;                  // not mentioned in IEEE (ISA) 1609.0-1609.4
}


/* ==========================================================================
*  communications primitives
*  ==========================================================================
*/

/* ----------------------------------------------------------------------------------
* set_device_mac_address - sets the device's MAC address
*
* Inputs:    none
* Outputs:   none
*
* Effects:   displays the current system's ethernet device's MAC address
* -----------------------------------------------------------------------------------
*/
void set_device_mac_address()
{
  int fd;
  struct ifreq ifr;
  char *iface = "eth0";       // devices have multiple MAC addresses, get the one for the ethernet interface
  unsigned char *mac;

  // open a TCP/IP family (AF_INET), datagram (SOCK_DGRAM) (i.e., UDP), IP-based (6) socket
  // >  see http:// man7.org/linux/man-pages/man2/socket.2.html and https:// www.frozentux.net/iptables-tutorial/other/protocols.txt
  fd = socket(AF_INET, SOCK_DGRAM, 0);
  if (fd < 0)
  {
    printf("Error opening socket in set_device_mac_address method.\n");
    return;
  }

  // set up for ioctl call to socket to get MAC address: why the socket was opened in the first place
  ifr.ifr_addr.sa_family = AF_INET;
  strncpy(ifr.ifr_name , iface , IFNAMSIZ-1);

  // retrieve hardware address associated with device fd
  ioctl(fd, SIOCGIFHWADDR, &ifr);
  if (errno != 0)
  {
    perror("Error retrieving mac address for hardware device in set_device_mac_address method");
    return; //exit routine and avoid setting macaddr
  }
  close(fd);

    mac = (unsigned char *)ifr.ifr_hwaddr.sa_data;      // NO!!!  data has to be copied to a buffer that will persist after routine terminates
  sprintf(macaddr, "%.2x:%.2x:%.2x:%.2x:%.2x:%.2x", mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);  //formats and sets the macaddr global - does not print
}

/* ----------------------------------------------------------------------------------
* transmit_packet - transmits a beacon packet every fifth of a second
*
* Inputs:    id - a provider ID, cast as a void *
* Outputs:   none
*
* Effect:   -.  runs indefinitely, transmitting packets every fifth of a second
*           -.  updates transmit count/drop count transmission statistics
*
* Design notes:
* -.  casting input, output to void * is required by PThreads
*
* @TODO@ document txpower, rate, and all other vars -> Find out what the settings should be and if and when they need to change ->
*  Establish the beacon frequency we actually need and set it (through a control parameter, not the current MN)
* @TODO@ make txpower, rate, txpriority, and sleep interval channel configuation parameters
* @TODO@ Use semaphores to guard access to statics
* @TODO@ Improve error handling - txWSMPacket() returns 65 EVERY TIME, even on FAILURE
* @TODO@ - Make sure that the SIG-handlers don't need to be included here, and that they can just be included in main()
* -----------------------------------------------------------------------------------
*/
void *transmit_packet(void *id)
{
  // ret is for holding the result code for txWSMPacket()
  // p_id holds the provider id

  int WMEStatusCode, p_id = *((int *)id);
  buildWSMRequestPacket(&wsmBeacon);

  while(1)
  {

    wsmBeacon.chaninfo.txpower = CONFIG.WSMRequest_ChanInfo_TXPower;
    wsmBeacon.chaninfo.rate = CONFIG.WSMRequest_ChanInfo_Rate;       // @TODO@ Document this
    wsmBeacon.txpriority = CONFIG.WSMRequest_TXPriority;             // @TODO@ not mentioned in IEEE (ISA) 1609.0-1609.4 PDFs, FIND WHERE IT IS MENTIONED

    usleep(200000);                     // transmit every fifth of a second @TODO@ make this a config item

    setBeaconPacketData();              // put the beacon data in the packet
    WMEStatusCode = txWSMPacket(p_id, &wsmBeacon);   // transmit the packet - returns 65 EVERY TIME, even on FAILURE

    if( WMEStatusCode < 0)      // if txWSMPacket signals success increment tx_packets, otherwise increment drops
    {
      drops++;
    }
    else
    {
      tx_packets++;
    }
  }
}

/* ----------------------------------------------------------------------------------
* receive_packet - receives and handles a beacon packet
*
* Inputs:    id - a provider ID, cast as a void *
* Outputs:   none
*
* Effect:   -.  runs indefinitely, receiving packets, logging them, and relaying them to the server
*           -.  updates receive count count transmission statistics
*
* @TODO@ document txpower and rate, explain rationale for sending a control packet every 10 receptions
* @TODO@ Remove print statement when debugging is complete - WHEN YOU'RE DONE
* @TODO@ (future implementation) May need to - if WMEStatusCode !> 0, then create check for amount of bytes from rxWSMPacket
* @TODO@ - Make sure that the SIG-handlers don't need to be included here, and that they can just be included in main()
* ------------------------------------------------------------------------------------
*/
void *receive_packet(void *id)
{
  int WMEStatusCode, p_id = *((int *)id);

  while(1)
  {
    // bzero(&rxpkt, sizeof(WSMIndication));
    WMEStatusCode = rxWSMPacket(pid, &rxpkt);  // rxWSMPacket returns -2 when no packets are received, and 65, 421, 369 for received (Find out what this means?)
    if (WMEStatusCode > 0) //if WMEStatusCode !> 0
    {
				process_message(rxpkt.data.contents+2); // for whatever reason, the plus 2 is needed to avoid a 0x0002 that pads the beginning of these packets. @TODO@ track down the cause of this and kill it.

/* @DEBUG@
        pthread_mutex_lock(&locks[1]);   // locks[1] guards printf
					// debugging prints
        	printf("-------- Received on channel %d ----------\n", rxpkt.chaninfo.channel);
					printf("%d\n", rxpkt.data.length);
					printf("%s\n", rxpkt.data.contents+2); // for whatever reason, the plus 2 is needed to avoid a 0x0002 that pads the beginning of these packets. @TODO@ track down the cause of this and kill it.
        	printf("--------/ Received on channel %d ----------\n", rxpkt.chaninfo.channel);
        pthread_mutex_unlock(&locks[1]);

*/
      if( (++rx_packets) % 10 == 0 )
      {
        setControlPacketData(&wsmControl);
        pthread_mutex_lock(&locks[1]);   // locks[1] guards printf
        printf("Control packet %s\n", txWSMPacket(p_id, &wsmControl) < 0 ? "dropped" : "sent");
        pthread_mutex_unlock(&locks[1]);
      }
    }
  }
}

/* ----------------------------------------------------------------------------------
* process_message - Checks to see if a message is from an RSU and intended for this
*                   OBU, then does some processing on it.
*
* Inputs:    char* message - the message to parse/process
* Outputs:   0 if message isn't a message for us from an RSU, 1 if it is.
*
* Effect:    none.
*
* Notes:     The format for a message is as follows:
*
*                [FROM_RSU_TOKEN]:[uuid]:[message]
*
*            eg.
*
*                FRSU:dba4467c-e2ce-4220-be82-2833ad98322a:fuck
*
*            is a message for dba4467c-e2ce-4220-be82-2833ad98322a that says "fuck"
*
*            Note: the current implementation doesn't check for the ":" at the end of
*            the GUID, since GUIDs are of fixed length (for our purposes). Instead,
*            it's assumed to be there, and we ignore that character when passing the
*            message on.
*            @TODO@ check for this delimiter instead of basing it on length.
*
*
* @TODO@ - Make this actually do something instead of print the message.
* ------------------------------------------------------------------------------------
*/
int process_message(char* message) {
	//is this from the RSU, and if so, is it  for us?
	if(strncmp(message, FROM_RSU_TOKEN, FROM_RSU_TOKEN_LEN) == 0 &&
     strncmp(message + FROM_RSU_TOKEN_LEN, CONFIG.uid, strlen(CONFIG.uid)) == 0) {
		 // yes, it's from an RSU and for us. do something.
		 // @TODO@ do whatever the RSU told us to do.
      pthread_mutex_lock(&locks[1]);   // locks[1] guards printf
				printf("Received the following message for us from the RSU: %s\n",message);
      pthread_mutex_unlock(&locks[1]);

			// forward this message to the phone
			if(bluetooth_client != -1) {
				write_server(message + FROM_RSU_TOKEN_LEN + strlen(CONFIG.uid) + 1);
			}

			return 1;
	}
	return 0;
}

/* ====================== BLUETOOTH RELATED CODE ============================== */
/* ----------------------------------------------------------------------------------
* init_server - initializes a bluetooth socket.
*
* Inputs:
* -. *sock        - the address to store the socket for the connection in
* -. *client      - the address to store the client for the connection in
* -. *port        - the address containing the port to use for the connection
*
* Outputs: none
*
* Effects: *sock and *client are now sockets and clients corresponding to the
*          created connection.
*
* Design notes:
* -. If any of the socket calls fails, this function returns early and errno is
*    left as whatever the socket-related function leaves it as. So, errno can be
*    checked to determine if this was successful or not
* -. @TODO@ - Rename. Ugh. The name is a remnant of Salman's naming scheme, and
*             doesn't accurately reflect what this function does.
* -----------------------------------------------------------------------------------
*/
void init_server(int *sock, int *client, int *port) {

	// local bluetooth adapter
	struct sockaddr_rc loc_addr = { 0 };
	loc_addr.rc_family = AF_BLUETOOTH;
	loc_addr.rc_bdaddr = *BDADDR_ANY;
	loc_addr.rc_channel = (uint8_t) *port;

	// register service
	sdp_session_t *session = register_service(*port);

	// allocate socket
	*sock = socket(AF_BLUETOOTH, SOCK_STREAM, BTPROTO_RFCOMM);
	if (*sock == -1 ) {
		perror("Error allocating socket");
		return;
	}
	printf("socket() returned %d\n", *sock);

	// bind socket
	int result = bind(*sock, (struct sockaddr *)&loc_addr, sizeof(loc_addr));
	if(errno != 0 ) {
		perror("Error binding to socket");
		printf("Port: %d\n", *port);
		return;
	}
	printf("bind() on channel %d returned %d\n", *port, result);
	printf("Port: %d\n", *port);

	// put socket into listening mode
	result = listen(*sock, 1);

	if(result == -1 ) {
		perror("Error listening to socket");
		return;
	}

	printf("listen() returned %d\n", result);

	// we've not accepted a connection here, so the client is dead
	*client = -1;

	/*
	// accept one connection
	printf("calling accept()\n");
	*client = accept(*sock, (struct sockaddr *)rem_addr, &opt);

	if(*client == -1 ) {
		perror("Error accepting connection from socket");
		return;
	}

	printf("accept() returned %d\n", *client);

	ba2str(&(rem_addr->rc_bdaddr), buffer);
	fprintf(stderr, "accepted connection from %s\n", buffer);
	memset(buffer, 0, sizeof(buffer));

  */

}

/* ----------------------------------------------------------------------------------
* write_server - Sends a string to the "bluetooth_client" (e.g. sends a string to the
*                phone)
*
* Inputs:
* -. *message  - the string to send to the socket.
*
* Outputs: 0 on failure, 1 on success. On failure, the client is cleared, and
*          errno is set to indicate the error.
*
* Effects: On failure, bluetooth_client is set to -1
*
* Design notes:
* -. If any of the socket calls fails, this function returns early and errno is
*    left as whatever the socket-related function leaves it as. So, errno can be
*    checked to determine if this was successful or not
* -. @TODO@ - Rename. Ugh. The name is a remnant of Salman's naming scheme, and
*             doesn't accurately reflect what this function does.
* -. @TODO@ - Pass a client to this instead of just calling hardcoding bluetooth_client
*             in it.
* -----------------------------------------------------------------------------------
*/
int write_server(char *message) {

	// see `man 3 write` for more details
	// write() writes to a pipe and returns a non-zero bytes_sent option on success
	int bytes_sent = write(bluetooth_client, message, strlen(message));
	if (bytes_sent > 0) {
		//printf("sent [%s] size = %d\n", messageArr, bytes_sent);
		return 1;
	}
	bluetooth_client = -1;
	return 0;
}

/* ----------------------------------------------------------------------------------
* clear_buffer - Rewrites a buffer with all 0x00
*
* Inputs:
* -. *buffer  - The buffer to clear.
* -. *len     - The length of the buffer
*
* Outputs: None
*
* Effects: The buffer is full of 0x00 bytes.
*
* Design notes: None
*
* @TODO@ can be cleaner or possibly faster with built in functions.
* -----------------------------------------------------------------------------------
*/
void clear_buffer(char* buffer, size_t len) {
	register int i;
	for(i = 0; i < len; i++) {
		buffer[i] = 0 ;
	}
}

/* ----------------------------------------------------------------------------------
* read_server - Reads a string from the "bluetooth_client" (e.g. reads a string from the
*                phone)
*
* Inputs: None
*
* Outputs: 0 on failure, 1 on success. On failure, the client is cleared, and
*          errno is set to indicate the error.
*
* Effects: On failure, bluetooth_client is set to -1
*
* Design notes:
* -. If any of the socket calls fails, this function returns early and errno is
*    left as whatever the socket-related function leaves it as. So, errno can be
*    checked to determine if this was successful or not
* -. There are two messages that interpreted as of now:
*
*    --. Duty change e.g. "DUTY:0" or "DUTY:1"
*    --. Occupancy change e.g. "OCCUPANCY:0" or "OCCUPANCY:1"
*
*    Duty change will change the dutyStatus to whatever byte follows the ":", as will
*    an occupancy change message with the occupancyStatus flag.
*
*    0 is false, 1 is true. Both the literal character '0' and the byte 0x00 are
*    interpreted as being zero. If 0 does not follow the ":", then the status
*    is set to true.
*
* -. @TODO@ - Rename. Ugh. The name is a remnant of Salman's naming scheme, and
*             doesn't accurately reflect what this function does.
* -. @TODO@ - Pass a client to this instead of just calling hardcoding bluetooth_client
*             in it.
* -. @TODO@ - Process the message in a meaningful way. As of now (12/2/17) it
*             just changes the duty and occupancy status
* -----------------------------------------------------------------------------------
*/
int read_server() {
	// the buffer in which to read in data
	char inBuffer[READ_BUFFER_SIZE];

	// read in the data
	int bytes_read = read(bluetooth_client, inBuffer, sizeof(inBuffer) - 1);

	// bytes_read > 0 indicates success
	if( bytes_read > 0 ) {
		// for now, simply print the received message.
		// @TODO@ process the messages
		printf("received [%s]\n", inBuffer);

		// see if this bt message is a "CHANGE UR FUKKEN DUTY STATUS BRO" message
		if(strncmp(inBuffer, DUTY_CHANGE_TOKEN, DUTY_CHANGE_TOKEN_LEN) == 0) {
			// this is a change duty status message, let's see what to change it to
			if (inBuffer[DUTY_CHANGE_TOKEN_LEN] == '0' || inBuffer[DUTY_CHANGE_TOKEN_LEN] == 0 ) {
				// 0 => set to false
				dutyStatus = false;
			}
			else {
				// non-zero => set to true.
				dutyStatus = true;
			}
		}
		// see if this bt message is a "CHANGE UR FUKKEN OCCUPANCY STATUS BRO" message
		if(strncmp(inBuffer, OCCUPANCY_CHANGE_TOKEN, OCCUPANCY_CHANGE_TOKEN_LEN) == 0) {
			// this is a change occupancy status message, let's see what to change it to
			if (inBuffer[OCCUPANCY_CHANGE_TOKEN_LEN] == '0' || inBuffer[OCCUPANCY_CHANGE_TOKEN_LEN] == 0 ) {
				// 0 => set to false
				occupancyStatus = false;
			}
			else {
				// non-zero => set to true.
				occupancyStatus = true;
			}		// change occupancy
		}

		// clear the inBuffer so we don't read bullshit next time.
		clear_buffer(inBuffer, sizeof(inBuffer));

		// we read stuff, so return 1
		return 1;
	}

	// we failed to read for some reason. kill the client and return -1
	bluetooth_client = -1;
	return 0;
}

/* ----------------------------------------------------------------------------------
* init_bt_server - initializes a bluetooth socket and continuously waits for a
*                  connection to it. Restarts waiting whenever a connection is
*                  dropped. Really, this is just a bluetooth thread
*
* Inputs:
* -. *ptr         - useless, for pthreads
* Outputs: none
*
* Effects: The corresponding sockets to the thread type are initialized and then
*          listened on until a connection happens. Then the code enters a loop
*          where it just checks to see if the client is dead, and if so, waits for
*          a new connection on it.
*
* Design notes:
* -. Used as a thread, hence the void* stuff.
* -. If any of the socket calls fails, this function returns early and errno is
*    left as whatever the socket-related function leaves it as. So, errno can be
*    checked to determine if this was successful or not
* -. @TODO@ - Rename. Ugh. The name is a remnant of Salman's naming scheme, and
*             doesn't accurately reflect what this function does, at all.
* -. @TODO@ - Rename void *ptr to something else. ptr is not an accurate name
* -----------------------------------------------------------------------------------
*/
void *init_bt_server(void *ptr){

	signal(SIGINT,(void *)sig_int);
	signal(SIGTERM,(void *)sig_term);

	// the client, socket, port, and remote address for this connection to use.
	// @TODO@ we can reference the client, sock, port, etc. directly. Just too lazy to
	// make that change while not at the lab.
	int *client = &bluetooth_client;
	int *sock = &bluetooth_sock;
	int *port = &BLUETOOTH_PORT;
	struct sockaddr_rc *rem_addr = &bluetooth_rem_addr;

	init_server(sock, client, port);

	// continuously check for connection drops and then new connections.
	while(1){
		// is the client dead?
		if(*client == -1){
		  // call accept() to get a new connection.
			printf("calling accept()\n");
			*client = accept(*sock, (struct sockaddr *)rem_addr, &opt);

			if(errno != 0) {
				perror("Error accepting connection to socket");
				return (void*)1;
			}

			printf("accept() returned %d\n", *client);

			// output address of connected device.
			ba2str(&(rem_addr->rc_bdaddr), buffer);
			fprintf(stderr, "accepted connection from %s\n", buffer);
			memset(buffer, 0, sizeof(buffer));
		}
	}
}
/* ================== END BLUETOOTH RELATED CODE ============================== */

/* ==========================================================================
*  main()
*  ==========================================================================
*
* main () - Begins by checking for correct command line parameters, then (does what?)
*
* Inputs:
*   argc (int) - count of command line arguments
*   argv (char *) - the arguments proper, as an array of strings
* Outputs:          XYZ
* Returns:
*   a status code  describe the values
* Effects:          XYZ
*
* Design Notes: ...
*
* @TODO@ - audit argv[] for correct number of parameters; argv[1]-argv[3] for in-range values
* @TODO@ - check buildPSTEntry, buildWMETARequest for success
* ----------------------------------------------------------------------------
*/
int main (int argc, char *argv[])
{
  int result, i, ret;
  pthread_t tx_thread, rx_thread;     // transmit and receive threads
	pthread_t bluetooth_read_thread;    // thread for reading from bluetooth
  uint8_t channel, channelinterval, channelAccess;
	occupancyStatus = true;
	dutyStatus = true;

  /* catch control-c, kill, and quit signals */
  signal(SIGINT,(void *)sig_int);
  signal(SIGTERM,(void *)sig_term);
  signal(SIGQUIT,(void *)sig_term);

	// try to read the config file
	printf("Reading configuration file\n");

	if(!setConfigItems(&CONFIG)) {
		// config file not read for some reason. Display error and die.
		perror("Error setting config items");
		exit(1);
	} // config file read successfully :)

  for(i = 0; i < 10; i++) // initialize semaphores
  {
     pthread_mutex_init(&locks[i], NULL);
  }
  for(i = 0; i < 10; i++) // initialize semaphores
  {
     sem_init(&stopLight[i], 0, 0);
  }

  pid = getpid();  // initialize this process's ID, for registering self and error reporting

	//store the mac address in macaddr
	set_device_mac_address();
	printf("MAC Address: %s\n", macaddr);

  if (argc < 4)         // check for correct minimum command line args
  {
    printf("usage: rxtx [sch channel access <0 - alternating> <1 - continous>] [TA channel ] [ TA channel interval <1- cch int> <2- sch int>] \n");
    return 0;
  }

  WMETARequest tareq; // static variable of a WMETARequest; built by buildWMETARequest
  channelAccess = atoi(argv[1]);
  channel = atoi(argv[2]);
  channelinterval = atoi(argv[3]);

  printf("Filling Provider Service Table entry.. \n");
  int buildPSTEntrySuccess = buildPSTEntry(channelAccess); //need to do something with potential buildPSTEntry failure return status
  printf("Building a WME Application Request\n");
  // buildWMEApplicationRequest();
  printf("Builing TA request\n");
  buildWMETARequest(&tareq, channel, channelinterval);

  if ( invokeWAVEDriver(0) < 0 )
  {
    printf( "Opening Failed.\n ");
    exit(-1);
  }
  printf("Driver invoked\n");

  printf("Invoking WAVE driver for receiver\n");
  if (invokeWAVEDevice(WAVEDEVICE_LOCAL, 0) < 0)
  {
    printf("Open Failed. Quitting\n");
    exit(-1);
  }

  printf("starting TA\n");
  if (transmitTA(&tareq) < 0)
  {
    printf("send TA failed\n ");
  }
  else
  {
    printf("send TA successful\n");
  }

  printf("Registering provider\n "); // this always fails, but the app seems to work, WTF?
  if ( registerProvider( pid, &entry ) < 0 )
  {
    printf("\nRegister Provider failed\n");
    removeProvider(pid, &entry); // if registration failed, what are we removing
    registerProvider(pid, &entry); // is this a retry? if so, how do we know success or failure?
  }
  else
  {
    printf("provider registered with PSID = %d\n", entry.psid );
  }

  printf("Creating TX thread...\n");
  ret = pthread_create(&tx_thread, NULL, transmit_packet, (void *)&pid);
  if(ret < 0){
    printf("Failed to create tx thread\n");
    exit(1);
  }

  printf("Creating RX thread...\n");
  ret = pthread_create(&tx_thread, NULL, receive_packet, (void *)&pid);
  if(ret < 0)
  {
    printf("Failed to create rx thread\n");
    exit(1);
  }

	// create the bluetooth threads
	printf("Creating bluetooth connection thread...\n");
	ret = pthread_create(&bluetooth_read_thread, NULL, init_bt_server, (void *)&pid);
	if(ret < 0){
		fprintf(stderr, "Error creating reading thread, error code: %d\n", ret);
		return 1;
	}

	// listen to bt client
	// @TODO@ this could be it's own thread, but since nothing else is going on in main,
	// I've left this here, even though it was placed there just for testing purposes.
	// Probs better practice to make its own thread
	while(1) {
		if(bluetooth_client != -1) {
			read_server();
		}
	}

	// thread maintenance
	pthread_join(bluetooth_read_thread, NULL);
  pthread_join(tx_thread, NULL);      // wait on these threads to finish their jobs before exiting
  pthread_join(rx_thread, NULL);
  return 1;
}


/* ===================== bluetooth register_service code ==============================
 * Note: this code is copy/pasta'd from salman's old bluetooth code, where he had
 * copy/pasta'd it from some open-source bluetooth project. Probably best to not chage
 * it and leave it alone. However, there is a UUID field and other meta-data at the
 * start of the function that we can safely change, related to what the bluetooth
 * connection is registered under.
 */

/* To compile this, use the following Bash command:
* gcc -I/usr/include/glib-2.0/ -I/usr/lib/glib-2.0/include -o server-with-haskell server-with-haskell.c -lbluetooth
*
* Adapted from http://www.btessentials.com/examples/examples.html, under the following license:
*
* Copyright (c) 2007 Albert Huang & Larry Rudolph
*
* Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation
* files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
* merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT
* LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
* DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

/* Allows this service to be discovered when running sdptool. For example, you can find this service
* after starting it by running
*
* $ sdptool browse local
*
* (Adapted from http://www.btessentials.com/examples/bluez/sdp-register.c)
* */
sdp_session_t *register_service(uint8_t rfcomm_channel) {

	/* A 128-bit number used to identify this service. The words are ordered from most to least
	* significant, but within each word, the octets are ordered from least to most significant.
	* For example, the UUID represneted by this array is 00001101-0000-1000-8000-00805F9B34FB. (The
	* hyphenation is a convention specified by the Service Discovery Protocol of the Bluetooth Core
	* Specification, but is not particularly important for this program.)
	*
	* This UUID is the Bluetooth Base UUID and is commonly used for simple Bluetooth applications.
	* Regardless of the UUID used, it must match the one that the Android app is searching
	* for.
	*/
	uint32_t svc_uuid_int[] = { 0x00001101, 0x00001000, 0x80000080, 0x5F9B34FB };
	const char *service_name = "ITHS Taxi Connection";
	const char *svc_dsc = "Connect to get some hails, bro";
	const char *service_prov = "ITHS";

	uuid_t root_uuid, l2cap_uuid, rfcomm_uuid, svc_uuid, svc_class_uuid;
	sdp_list_t *l2cap_list = 0,
		   *rfcomm_list = 0,
		   *root_list = 0,
		   *proto_list = 0,
		   *access_proto_list = 0,
		   *svc_class_list = 0,
		   *profile_list = 0;

	sdp_data_t *channel = 0;
	sdp_profile_desc_t profile;
	sdp_record_t record = { 0 };
	sdp_session_t *session = 0;

	// set the general service ID
	sdp_uuid128_create(&svc_uuid, &svc_uuid_int);
	sdp_set_service_id(&record, svc_uuid);

	char str[256] = "";
	sdp_uuid2strn(&svc_uuid, str, 256);
	printf("Registering UUID %s\n", str);
	printf("Registering channel %d\n", rfcomm_channel);

	// set the service class
	sdp_uuid16_create(&svc_class_uuid, SERIAL_PORT_SVCLASS_ID);
	svc_class_list = sdp_list_append(0, &svc_class_uuid);
	sdp_set_service_classes(&record, svc_class_list);

	// set the Bluetooth profile information
	sdp_uuid16_create(&profile.uuid, SERIAL_PORT_PROFILE_ID);
	profile.version = 0x0100;
	profile_list = sdp_list_append(0, &profile);
	sdp_set_profile_descs(&record, profile_list);

	// make the service record publicly browsable
	sdp_uuid16_create(&root_uuid, PUBLIC_BROWSE_GROUP);
	root_list = sdp_list_append(0, &root_uuid);
	sdp_set_browse_groups(&record, root_list);

	// set l2cap information
	sdp_uuid16_create(&l2cap_uuid, L2CAP_UUID);
	l2cap_list = sdp_list_append(0, &l2cap_uuid);
	proto_list = sdp_list_append(0, l2cap_list);

	// register the RFCOMM channel for RFCOMM sockets
	sdp_uuid16_create(&rfcomm_uuid, RFCOMM_UUID);
	channel = sdp_data_alloc(SDP_UINT8, &rfcomm_channel);
	rfcomm_list = sdp_list_append(0, &rfcomm_uuid);
	sdp_list_append(rfcomm_list, channel);
	sdp_list_append(proto_list, rfcomm_list);

	access_proto_list = sdp_list_append(0, proto_list);
	sdp_set_access_protos(&record, access_proto_list);

	// set the name, provider, and description
	sdp_set_info_attr(&record, service_name, service_prov, svc_dsc);

	// connect to the local SDP server, register the service record,
	// and disconnect
	session = sdp_connect(BDADDR_ANY, BDADDR_LOCAL, SDP_RETRY_IF_BUSY);
	sdp_record_register(session, &record, 0);

	// cleanup
	sdp_data_free(channel);
	sdp_list_free(l2cap_list, 0);
	sdp_list_free(rfcomm_list, 0);
	sdp_list_free(root_list, 0);
	sdp_list_free(access_proto_list, 0);
	sdp_list_free(svc_class_list, 0);
	sdp_list_free(profile_list, 0);

	return session;
}
